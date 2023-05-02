{-# LANGUAGE TupleSections, FlexibleContexts, PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Types.IMonad where

import Utils
import AST
import Types.Unification
import Types.Schemes
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Arrow (first, second)
import Control.Category (Category(..))
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Stream as SM
import Prelude hiding ((.))

type IMonad v a b = ReaderT (TypeContext v a, DataCtors a)
                              (StateT (TySubst a a, SM.Stream a)
                                (Except String)) b
type TypeContext b a = M.Map b (TypeScheme a)
type DataCtors a = M.Map CtorName (TypeScheme a)

runIMonad :: TypeContext v a
          -> DataCtors a
          -> TySubst a a
          -> SM.Stream a
          -> IMonad v a b
          -> Except String _
runIMonad tc dc sub str m = runStateT (runReaderT m (tc, dc)) (sub, str)

generalizeM :: _ => Type a -> IMonad v a (TypeScheme a)
generalizeM ty = do
  tyy <- applyCurrentSub ty
  ftvs <- freeTypeVarsInContext
  return $ generalize ftvs tyy

infix 4 +|-
(+|-) :: (Ord a, Ord v)
      => [(v, Type a)] -> IMonad v a b -> IMonad v a b
bs +|- m = foldr (uncurry pushContext . second SMono) m bs

infix 4 +|-^
(+|-^) :: (Ord a, Ord v)
      => [(v, Type a)] -> IMonad v a b -> IMonad v a b
bs +|-^ m = do
  bs' <- forM bs $ secondM generalizeM
  let f = flip (foldr $ uncurry M.insert) bs'
  withCtxtTrans f m

infix 4 +|-^^
(+|-^^) :: (Ord a, Ord v)
        => [(v, TypeScheme a)] -> IMonad v a b -> IMonad v a b
bs +|-^^ m = withCtxtTrans (flip (foldr $ uncurry M.insert) bs) m

pushContext :: _ => v -> TypeScheme a -> IMonad v a b -> IMonad v a b
pushContext v t = withCtxtTrans (M.insert v t)

withCtxtTrans :: (TypeContext v a -> TypeContext v a)
              -> IMonad v a b -> IMonad v a b
withCtxtTrans f = local (first f)

unify :: _ => [UnifEquation a] -> IMonad v a ()
unify eqs = do
  cSub <- currentSub
  (lift . lift $ unifySet cSub eqs) >>= pushSub

setSub :: TySubst a a -> IMonad v a ()
setSub sub = do
  (cSub,x) <- get
  put (sub,x)

pushSub :: TySubst a a -> IMonad v a ()
pushSub sub = do
  cSub <- currentSub
  setSub $ sub . cSub

currentSub :: IMonad v a (TySubst a a)
currentSub = fst <$> get

freeTypeVarsInContext :: Ord a => IMonad v a (S.Set a)
freeTypeVarsInContext =
  M.foldr S.union S.empty . M.map schemeFreeVars <$> context

context :: IMonad v a (TypeContext v a)
context = fst <$> ask

dataCtors :: IMonad v a (DataCtors a)
dataCtors = snd <$> ask

getStream :: IMonad v a (SM.Stream a)
getStream = snd <$> get

putStream :: SM.Stream a -> IMonad v a ()
putStream str = do
  (x,_) <- get
  put (x,str)

applyCurrentSubS :: TypeScheme a -> IMonad v a (TypeScheme a)
applyCurrentSubS sc = do
  cSub <- currentSub
  return $ schemeSub cSub sc

applyCurrentSub :: Type a -> IMonad v a (Type a)
applyCurrentSub ty = do
  cSub <- currentSub
  return $ subType cSub ty

applyCurrentSubV :: a -> IMonad v a (Type a)
applyCurrentSubV x = do
  cSub <- currentSub
  return $ applyTS cSub x

schemeOfVar :: _ => v -> IMonad v a (TypeScheme a)
schemeOfVar x = do
  gamma <- context
  maybe (throwError errMsg) applyCurrentSubS (M.lookup x gamma)
  where errMsg = "symbol " ++ show x ++ " not in context"

newVar :: IMonad v a a
newVar = do
  (SM.Cons x stream) <- getStream
  putStream stream
  return x

takeNewVars :: Int -> IMonad v a [a]
takeNewVars n = replicateM n newVar

fullyInstM :: TypeScheme a -> IMonad v a (Type a)
fullyInstM sc = do
  (ty, str) <- fullyInst sc <$> getStream
  putStream str
  return ty
