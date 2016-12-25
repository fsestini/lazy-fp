{-# LANGUAGE TupleSections, FlexibleContexts, PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Types.IMonad where

import Control.Arrow (first, second)
import Utils
import qualified Data.Map as M
import qualified Data.List.NonEmpty as NE
import AST
import AssocList
import Types.Unification
import Types.Schemes
import Control.Monad.Except
import Core.CaseStripping
import Control.Monad.Reader
import Control.Monad.State
import RecursionSchemes
import Control.Monad.Trans
import qualified Data.Set as S
import qualified Data.Stream as SM
import PickFresh
import Core.Syntax

type IMonad v a b = ReaderT (TypeContext v a, DataCtors a)
                              (StateT (SM.Stream a) (Except String)) b
type IMonadRes v a = IMonad v a (TySubst a a, Type a)
type TypeContext b a = M.Map b (TypeScheme a)
type DataCtors a = M.Map CtorName (TypeScheme a)

runIMonad :: TypeContext v a
          -> DataCtors a
          -> SM.Stream a
          -> IMonad v a b
          -> Except String (b, SM.Stream a)
runIMonad tc dc str m = runStateT (runReaderT m (tc, dc)) str

generalizeM :: _ => Type a -> IMonad v a (TypeScheme a)
generalizeM ty = flip generalize ty <$> freeTypeVarsInContext

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

locCSub :: TySubst a a -> IMonad v a b -> IMonad v a b
locCSub phi = local (first $ ctxtSub phi)

unifyM :: _ => [UnifEquation a] -> IMonad v a (TySubst a a)
unifyM eqs = lift . lift $ unify eqs

ctxtSub :: TySubst a b -> TypeContext c a -> TypeContext c b
ctxtSub phi = M.map (schemeSub phi)

freeTypeVarsInContext :: Ord a => IMonad v a (S.Set a)
freeTypeVarsInContext =
  M.foldr S.union S.empty . M.map schemeFreeVars <$> context

context :: IMonad v a (TypeContext v a)
context = fst <$> ask

dataCtors :: IMonad v a (DataCtors a)
dataCtors = snd <$> ask

getStream :: IMonad v a (SM.Stream a)
getStream = get

putStream :: SM.Stream a -> IMonad v a ()
putStream = put

schemeOfVar :: _ => v -> IMonad v a (TypeScheme a)
schemeOfVar x = do
  gamma <- context
  maybe (fail errMsg) return (M.lookup x gamma)
  where errMsg = "symbol " ++ show x ++ " not in context"

newVar :: IMonad v a a
newVar = do
  (SM.Cons x stream) <- get
  put stream
  return x

takeNewVars :: Int -> IMonad v a [a]
takeNewVars n = replicateM n newVar

fullyInstM :: TypeScheme a -> IMonad v a (Type a)
fullyInstM sc = do
  (ty, str) <- fullyInst sc <$> getStream
  putStream str
  return ty
