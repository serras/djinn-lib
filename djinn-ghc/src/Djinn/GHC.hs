{-# LANGUAGE PatternGuards #-}
module Djinn.GHC (Environment, djinn) where

import Control.Monad (forM)
import Data.Set (Set, insert, union, unions, empty, toList)

import qualified Djinn.HTypes as D
import qualified Djinn.LJT as D

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

environment :: G.GhcMonad m => G.Type -> m HEnvironment
environment = fmap concat . mapM environment1 . toList . getConTs

environment1 :: G.GhcMonad m => G.Name -> m HEnvironment
environment1 name = do
  thing <- G.lookupGlobalName name
  case thing of
    Just (G.ATyCon tycon) | G.isAlgTyCon tycon -> do
      let tyconName = toHSymbol $ G.tyConName tycon
          varsH = map toHSymbol $ G.tyConTyVars tycon
          Just datacons = G.tyConDataCons_maybe tycon
      dtypes <- forM datacons $ \dcon -> do
        let dconN = toHSymbol $ G.dataConName dcon
            (_,_,dconT,_) = G.dataConSig dcon
        dconE <- mapM environment dconT
        return ((dconN, map hType dconT), dconE)
      let dtypesT = map fst dtypes
          dtypesE = concatMap snd dtypes
      return $ (tyconName, (varsH, D.HTUnion dtypesT, NoExtraInfo)) : concat dtypesE
    Just (G.ATyCon tycon) | G.isSynTyCon tycon -> do
      -- Get information for this type synonym
      let tyconName = toHSymbol $ G.tyConName tycon
          Just (vars, defn) = G.synTyConDefn_maybe tycon
          varsH = map toHSymbol vars
          htype = hType defn
      -- Recursively obtain it for the environment of the type
      defnEnv <- environment defn
      return $ (tyconName, (varsH, htype, NoExtraInfo)) : defnEnv
    _ -> return []

toHSymbol :: G.NamedThing a => a -> D.HSymbol
toHSymbol = G.getOccString

toLJTSymbol :: G.NamedThing a => a -> D.Symbol
toLJTSymbol = D.Symbol . G.getOccString

-- |Bindings which are in scope at a specific point.
type Environment = [(G.Name, G.Type)]

-- |Obtain the list of expressions which could fill
-- something with the given type.
-- The first flag specifies whether to return one
-- or more solutions to the problem.
djinn :: G.GhcMonad m => Bool -> Environment -> G.Type -> m [String]
djinn multi env ty = do
  tyEnv <- environment ty
  let form = D.hTypeToFormula tyEnv (hType ty)
      envF = map (\(n,t) -> (toLJTSymbol n, D.hTypeToFormula tyEnv (hType t))) env
      prfs = D.prove multi envF form
  return $ map (D.hPrExpr . D.termToHExpr) prfs
