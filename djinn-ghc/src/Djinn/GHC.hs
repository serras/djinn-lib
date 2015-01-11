{-# LANGUAGE CPP, PatternGuards, BangPatterns #-}
module Djinn.GHC (Environment, MaxSolutions(..), djinn) where

import Control.Concurrent
import Control.Concurrent.Async
import Control.Monad (forM)
import Data.Maybe (isJust)
import Data.Set (Set, insert, union, unions, empty, toList)

import qualified Djinn.HTypes as D
import qualified Djinn.LJT as D

import MonadUtils
import qualified DataCon as G
import qualified GHC as G
import qualified Name as G
import qualified TyCon as G
import qualified Type as G

data NoExtraInfo = NoExtraInfo
type HEnvironment1 a = [(D.HSymbol, ([D.HSymbol], D.HType, a))]
type HEnvironment = HEnvironment1 NoExtraInfo

getConTs :: G.Type -> Set G.Name
getConTs t | Just (_, i)  <- G.splitForAllTy_maybe t = getConTs i
getConTs t | Just (t1,t2) <- G.splitFunTy_maybe t    = getConTs t1 `union` getConTs t2
getConTs t | Just (c, ts) <- G.splitTyConApp_maybe t = 
  let args = unions $ map getConTs ts
   in if G.isTupleTyCon c then args else insert (G.getName c) args
getConTs t | Just (t1,t2) <- G.splitAppTy_maybe t    = getConTs t1 `union` getConTs t2
getConTs t | Just _       <- G.getTyVar_maybe t      = empty
getConTs _                                           = empty

hType :: G.Type -> D.HType
hType t | Just (_, i)  <- G.splitForAllTy_maybe t = hType i
hType t | Just (t1,t2) <- G.splitFunTy_maybe t    = D.HTArrow (hType t1) (hType t2)
hType t | Just (c, ts) <- G.splitTyConApp_maybe t =
  let args = map hType ts
   in if G.isTupleTyCon c  -- Check if we have a tuple
         then D.HTTuple args
         else createHTApp (G.getOccString c) (reverse args)
  where createHTApp n []     = D.HTCon n
        createHTApp n (x:xs) = D.HTApp (createHTApp n xs) x
hType t | Just (t1,t2) <- G.splitAppTy_maybe t    = D.HTApp (hType t1) (hType t2)
hType t | Just var <- G.getTyVar_maybe t          = D.HTVar (toHSymbol var)
hType _                                           = error "Unimplemented"

environment :: G.GhcMonad m => Maybe G.ModuleInfo -> G.Type -> m HEnvironment
environment minfo = fmap concat . mapM (environment1 minfo) . toList . getConTs

environment1 :: G.GhcMonad m => Maybe G.ModuleInfo -> G.Name -> m HEnvironment
environment1 minfo name = do
  thing <- lookupNameEverywhere minfo name
  case thing of
    Just (G.ATyCon tycon) | G.isAlgTyCon tycon -> do
      let tyconName = toHSymbol $ G.tyConName tycon
          varsH = map toHSymbol $ G.tyConTyVars tycon
          Just datacons = G.tyConDataCons_maybe tycon
      dtypes <- forM datacons $ \dcon -> do
        let dconN = toHSymbol $ G.dataConName dcon
            (_,_,dconT,_) = G.dataConSig dcon
        dconE <- mapM (environment minfo) dconT
        return ((dconN, map hType dconT), dconE)
      let dtypesT = map fst dtypes
          dtypesE = concatMap snd dtypes
      return $ (tyconName, (varsH, D.HTUnion dtypesT, NoExtraInfo)) : concat dtypesE
#if __GLASGOW_HASKELL__ >= 710
    Just (G.ATyCon tycon) | G.isTypeSynonymTyCon tycon -> do
#else
    Just (G.ATyCon tycon) | G.isSynTyCon tycon -> do
#endif
      -- Get information for this type synonym
      let tyconName = toHSymbol $ G.tyConName tycon
#if __GLASGOW_HASKELL__ >= 708
          Just (vars, defn) = G.synTyConDefn_maybe tycon
#else
          (vars, defn) = G.synTyConDefn tycon
#endif
          varsH = map toHSymbol vars
          htype = hType defn
      -- Recursively obtain it for the environment of the type
      defnEnv <- environment minfo defn
      return $ (tyconName, (varsH, htype, NoExtraInfo)) : defnEnv
    _ -> return []

lookupNameEverywhere :: G.GhcMonad m => Maybe G.ModuleInfo -> G.Name -> m (Maybe G.TyThing)
lookupNameEverywhere (Just minfo) name = do
  thing <- G.modInfoLookupName minfo name
  if isJust thing then return thing else G.lookupGlobalName name
lookupNameEverywhere Nothing    name = G.lookupGlobalName name

toHSymbol :: G.NamedThing a => a -> D.HSymbol
toHSymbol = G.getOccString

toLJTSymbol :: G.NamedThing a => a -> D.Symbol
toLJTSymbol = D.Symbol . G.getOccString

-- |Bindings which are in scope at a specific point.
type Environment = [(G.Name, G.Type)]

-- |Obtain a maximum number of solutions.
newtype MaxSolutions = Max Int

-- |Obtain the list of expressions which could fill
-- something with the given type.
-- The first flag specifies whether to return one
-- or more solutions to the problem.
djinn :: G.GhcMonad m => Bool -> Maybe G.ModuleInfo -> Environment -> G.Type -> MaxSolutions -> Int -> m [String]
djinn multi minfo env ty (Max mx) microsec = do
  tyEnv <- environment minfo ty
  let form = D.hTypeToFormula tyEnv (hType ty)
      envF = map (\(n,t) -> (toLJTSymbol n, D.hTypeToFormula tyEnv (hType t))) env
      prfs = D.prove multi envF form
      trms = map (D.hPrExpr . D.termToHExpr) prfs
  liftIO $ cropList trms microsec mx (\x -> lengthLessThan x 1000)

cropList :: [a] -> Int -> Int -> (a -> Bool) -> IO [a]
cropList _   _  0 _ = return []
cropList lst ms n chk =
  withAsync (let !l = lst in return l) $ \a -> do
    threadDelay ms
    res <- poll a
    case res of
      Just r -> case r of
        Right (x:xs) -> if chk x then do ys <- cropList xs ms (n-1) chk
                                         return $ x : ys
                                 else return []
        _            -> return []
      Nothing -> do cancel a
                    return []

lengthLessThan :: [a] -> Int -> Bool
lengthLessThan []     _ = True
lengthLessThan (_:_)  0 = False
lengthLessThan (x:xs) n = lengthLessThan xs (n-1)
