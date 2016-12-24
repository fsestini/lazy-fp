{-# LANGUAGE TupleSections, FlexibleContexts, PartialTypeSignatures #-}

module Types.Inference where

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

inferExpr :: _ => DataCtors a -> CoreExpr v -> Except String (Type a)
inferExpr dc e = snd . fst <$> runIMonad M.empty dc (freshStream []) (infer e)

liftUnifRes :: UnifRes a -> ReaderT r (StateT s (Except String)) a
liftUnifRes = lift . lift

ctxtSub :: TySubst a b -> TypeContext c a -> TypeContext c b
ctxtSub phi = fmap (schemeSub phi)

freeTypeVarsInContext :: Ord a => IMonad v a (S.Set a)
freeTypeVarsInContext =
  M.foldr S.union S.empty . fmap schemeFreeVars <$> context

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

-- type TypeEnv a = S.Set (TypeDecl a)
-- newtype TypeDecl a = TD (a, TypeScheme a)
-- instance Eq a => Eq (TypeDecl a) where
--   (TD (x,_)) == (TD (y,_)) = x == y
-- instance Ord a => Ord (TypeDecl a) where
--   compare (TD (x,_)) (TD (y,_)) = compare x y

newVar :: IMonad v a a
newVar = do
  (SM.Cons x stream) <- get
  put stream
  return x

fullyInstM :: TypeScheme a -> IMonad v a (Type a)
fullyInstM sc = do
  (ty, str) <- fullyInst sc <$> getStream
  putStream str
  return ty

infer :: (Ord v, Show v, Ord a) => CoreExpr v -> IMonadRes v a
infer (EVar x) = inferVar x
infer (EApp e1 e2) = inferApp e1 e2
infer (ECtor name) = inferCtor name
infer (ELit (LInt n)) = return (idSub, intTy)
infer (ELet NonRecursive bs e) = inferLet (NE.toList bs) e
infer (ELet Recursive bs e) = inferLetrec (NE.toList bs) e
infer (ELam x e) = inferLambda x e
infer EErr = (idSub,) . MFree <$> newVar
infer (EPrim Add) = return (idSub, intTy --> intTy --> intTy)
infer (EPrim Sub) = return (idSub, intTy --> intTy --> intTy)
infer (EPrim Mul) = return (idSub, intTy --> intTy --> intTy)
infer (EPrim Eql) = return (idSub, intTy --> intTy --> boolTy)
infer (ECase e a) = inferCase e a

{-

case e of
  C1 x11 x12 .. x1m1 -> e1
  C2 x21 x22 .. x2m2 -> e2
  ...
  Cn xn1 xn2 .. xnmn -> en

Γ ⊢ e : τ
Γ, x11 : τ11, x12 : τ12, ..., x1m1 : τ1m1 ⊢ C1 x11 x12 ... x1m1 : τ
...
Γ, xn1 : τn1, xn2 : τn2, ..., xnmn : τnmn ⊢ Cn xn1 xn2 ... xnmn : τ
Γ, x11 : τ11, x12 : τ12, ..., x1m1 : τ1m1 ⊢ e1 : τ'
...
Γ, xn1 : τn1, xn2 : τn2, ..., xnmn : τnmn ⊢ en : τ'
---------------------------------------------------------------------
Γ ⊢ case e of ... : τ'


-}

inferCase :: _ => CoreExpr v -> NE.NonEmpty (AlterB v (CoreExpr v)) -> IMonadRes v a
inferCase e a = do
  (phi, scrTy) <- infer e
  (psi, ty) <- locCSub phi (inferAlters scrTy a)
  return (psi <> phi, ty)

inferAlter :: _ => Type a -> AlterB v (CoreExpr v) -> IMonadRes v a
inferAlter scrType (AlterB name vars e) = do
  freshTypeVars <- replicateM (length vars) newVar
  let ctxtAddition = zip vars (map MFree freshTypeVars)
      term = foldl EApp (ECtor name) (map EVar vars)
  (phi, t) <- ctxtAddition +|- infer term
  unifier <- liftUnifRes $ unify [(t, scrType)]
  let newDecls = zip vars $ map (unifier <> phi) freshTypeVars
  (psi, ty) <- locCSub (unifier <> phi) (newDecls +|- infer e)
  return (psi <> unifier <> phi, ty)

inferAlters :: _ => Type a -> NE.NonEmpty (AlterB v (CoreExpr v)) -> IMonadRes v a
inferAlters scrType a = flip foldr1 (fmap (inferAlter scrType) a) $ \ a as -> do
  (phi, t1) <- a
  (psi, t2) <- locCSub phi as
  unifier <- liftUnifRes $ unify [(subType psi t1, t2)]
  return (unifier <> psi <> phi, subType unifier t2)

locCSub :: TySubst a a -> IMonad v a b -> IMonad v a b
locCSub phi = local (first $ ctxtSub phi)

inferCtor :: _ => CtorName -> IMonadRes v a
inferCtor name = do
  ctors <- dataCtors
  maybe (fail errMsg) (return . (idSub,) <=< fullyInstM) $ M.lookup name ctors
  where errMsg = "data constructor " ++ name ++ " not in scope"

inferVar :: _ => v -> IMonadRes v a
inferVar = return . (idSub,) <=< fullyInstM <=< schemeOfVar

inferApp :: _ => CoreExpr v -> CoreExpr v -> IMonadRes v a
inferApp e1 e2 = do
  (s1, ty1) <- infer e1
  (s2, ty2) <- locCSub s1 (infer e2)
  beta <- newVar
  unifier <- liftUnifRes $ unify [(subType s2 ty1, ty2 --> MFree beta)]
  return (unifier <> s2 <> s1, unifier beta)

withCtxtTrans :: (TypeContext v a -> TypeContext v a)
              -> IMonad v a b -> IMonad v a b
withCtxtTrans f = local (first f)

inferLambda :: _ => v -> CoreExpr v -> IMonadRes v a
inferLambda x e = do
  beta <- newVar
  (s, ty) <- withCtxtTrans (M.insert x (SMono (MFree beta))) (infer e)
  return (s, s beta --> ty)

inferList :: _ => [CoreExpr v] -> IMonad v a (TySubst a a, [Type a])
inferList = foldr (f . infer) (return (idSub, []))
  where f e es = do
          (phi, t) <- e
          (psi, ts) <- locCSub phi es
          return (psi <> phi, subType psi t : ts)

inferLet :: _ => [BinderB v (CoreExpr v)] -> CoreExpr v -> IMonadRes v a
inferLet b e = do
  (phi, ts) <- inferList . map binderBody $ b
  let bVars = map binderVar b
  (psi, t) <- locCSub phi (zip bVars ts +|-^ infer e)
  return (psi <> phi, t)

generalizeM :: _ => Type a -> IMonad v a (TypeScheme a)
generalizeM ty = flip generalize ty <$> freeTypeVarsInContext

infix 4 +|-
(+|-) :: (Ord a, Ord v)
      => [(v, Type a)] -> IMonad v a b -> IMonad v a b
bs +|- m = foldr (uncurry pushContext . second SMono) m bs

infix 4 +|-^
(+|-^) :: (Ord a, Ord v)
      => [(v, Type a)] -> IMonadRes v a -> IMonadRes v a
bs +|-^ m = do
  bs' <- forM bs $ secondM generalizeM
  let f = flip (foldr $ uncurry M.insert) bs'
  withCtxtTrans f m

pushContext :: _ => v -> TypeScheme a -> IMonad v a b -> IMonad v a b
pushContext v t = withCtxtTrans (M.insert v t)

inferLetrec :: _ => [BinderB v (CoreExpr v)] -> CoreExpr v -> IMonadRes v a
inferLetrec bs e = do
  let vars = map binderVar bs
      bodies = map binderBody bs
  tyVars <- replicateM (length bs) newVar
  (phi, ts) <- zip vars (map MFree tyVars) +|- inferList bodies
  unifier <- liftUnifRes $ unify $ zip ts (map phi tyVars)
  let ts'' = map (unifier <> phi) tyVars
  (psi, t) <- locCSub (unifier <> phi) (zip vars ts'' +|-^ infer e)
  return (psi <> unifier <> phi, t)
