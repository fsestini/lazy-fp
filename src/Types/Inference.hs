{-# LANGUAGE GADTs, ScopedTypeVariables, TupleSections, FlexibleContexts,
             PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Types.Inference where

import Pair
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
import Types.IMonad
import Types.DataDecl
import Types.Fin
import Core.DependencyAnalysis

-- TODO change this:
-- it is better to use a GADT where type constructors parameterized
-- by their arity, to enhance type safety and static guarantees

checkArities :: [DataDecl a] -> Scheme n a -> Except String ()
checkArities decls (SForall sc) = checkArities decls sc
checkArities decls (SMono mono) = checkArities' mono
  where
    kindToArity KStar = 0
    kindToArity (KArrow _ k) = 1 + kindToArity k
    ddToPair (name, kind, _) = (name, kindToArity kind)
    aritiesMap = M.fromList $ map ddToPair decls
    checkArities' :: Monotype n a -> Except String ()
    checkArities' (MFree t) = return ()
    checkArities' (MBound t) = return ()
    checkArities' (MCtor name tys) =
      case M.lookup name aritiesMap of
        Nothing -> fail $ name ++ "type constructor " ++ name ++ " not in scope"
        (Just arity) -> if arity == length tys
          then forM_ tys checkArities'
          else fail $ "type constructor " ++ name ++ " has arity "
               ++ show arity ++ ", but it was applied to "
               ++ show (length tys) ++ " types"

checkReturnType :: CtorName -> Scheme n a -> Except String ()
checkReturnType parentTyName (SForall sc) = checkReturnType parentTyName sc
checkReturnType parentTyName (SMono mono) = checkReturnType' mono
  where
    failure = fail $ "data constructor for type " ++ parentTyName
              ++ " should return an element of type " ++ parentTyName
    checkReturnType' (MFree m) = failure
    checkReturnType' (MBound m) = failure
    checkReturnType' (ArrowTy _ t) = checkReturnType' t
    checkReturnType' (MCtor name _) = unless (name == parentTyName) failure

checkDataDecl :: [DataDecl a] -> DataDecl a -> Except String ()
checkDataDecl decls (name, _, ctorDecls) =
  forM_ ctorDecls (\(_, scheme) ->
    checkArities decls scheme >> checkReturnType name scheme)

fromDataDecls :: [DataDecl a] -> Except String (DataCtors a)
fromDataDecls decls' = forM_ decls' (checkDataDecl decls) >>
  (return . M.fromList . join . map (\(_,_,x) -> NE.toList x) $ decls')
  where decls = arrowDecl : decls'
        biKind = KArrow1 (KArrow1 KStar1)
        mono = MBound (FSucc FZero)
               --> MBound FZero
               --> MCtor "arrow" [MBound (FSucc FZero), MBound FZero]
        arrowDecl :: DataDecl a
        arrowDecl = ("arrow", biKind,
          ("arrowCtor", SForall (SForall (SMono mono))) NE.:| [])

inferExpr :: _ => [DataDecl a] -> CoreExpr v -> Except String (Type a)
inferExpr dd e = do
  dc <- fromDataDecls dd
  snd . fst <$> runIMonad M.empty dc (freshStream []) (infer e)

inferCoreScDefns :: forall a v . (Ord a, Ord v, Show v, PickFresh a)
                 => [DataDecl a]
                 -> [CoreScDefn v]
                 -> Except String [(CoreScDefn v, TypeScheme a)]
inferCoreScDefns decls defns = do
  dc <- fromDataDecls decls
  fst <$> runIMonad M.empty dc (freshStream [] :: SM.Stream a) inferred
  where depAn = map (second depAnalysisTrans) defns
        classified = classifyDefns depAn
        inferred = inferClassifications classified

inferClassifications :: _
                     => [Classification v]
                     -> IMonad v a [(CoreScDefn v, TypeScheme a)]
inferClassifications []  = return []
inferClassifications (ClNonRecursive (x,e) : cls) = do
  ty <- snd <$> infer e
  sc <- generalizeM ty
  ts <- pushContext x sc (inferClassifications cls)
  return $ ((x,e), sc) : ts
inferClassifications (ClRecursive pairs : cls) = do
  ts <- snd <$> inferMutrec pairs
  sc <- forM ts generalizeM
  let decls = zip (map fst pairs) sc
  sc' <- decls +|-^^ inferClassifications cls
  return $ zip pairs sc ++ sc'

infer :: (Ord v, Show v, Ord a) => CoreExpr v -> IMonadRes v a
infer (EVar x) = inferVar x
infer (EApp e1 e2) = inferApp e1 e2
infer (ECtor name) = inferCtor name
infer (ELit (LInt n)) = return (idSub, IntTy)
infer (ELet NonRecursive bs e) = inferLet (NE.toList bs) e
infer (ELet Recursive bs e) = inferLetrec (NE.toList bs) e
infer (ELam x e) = inferLambda x e
infer EErr = (idSub,) . MFree <$> newVar
infer (EPrim Add) = return (idSub, IntTy --> IntTy --> IntTy)
infer (EPrim Sub) = return (idSub, IntTy --> IntTy --> IntTy)
infer (EPrim Mul) = return (idSub, IntTy --> IntTy --> IntTy)
infer (EPrim Eql) = return (idSub, IntTy --> IntTy --> BoolTy)
infer (ECase e a) = inferCase e a

inferCase :: _
          => CoreExpr v
          -> NE.NonEmpty (AlterB v (CoreExpr v))
          -> IMonadRes v a
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
  unifier <- unifyM [(t, scrType)]
  let newDecls = zip vars $ map (unifier <> phi) freshTypeVars
  (psi, ty) <- locCSub (unifier <> phi) (newDecls +|- infer e)
  return (psi <> unifier <> phi, ty)

inferAlters :: _
            => Type a
            -> NE.NonEmpty (AlterB v (CoreExpr v))
            -> IMonadRes v a
inferAlters scrType a = flip foldr1 (fmap (inferAlter scrType) a) $ \ a as -> do
  (phi, t1) <- a
  (psi, t2) <- locCSub phi as
  unifier <- unifyM [(subType psi t1, t2)]
  return (unifier <> psi <> phi, subType unifier t2)

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
  unifier <- unifyM [(subType s2 ty1, ty2 --> MFree beta)]
  return (unifier <> s2 <> s1, unifier beta)

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

inferLetrec :: _ => [BinderB v (CoreExpr v)] -> CoreExpr v -> IMonadRes v a
inferLetrec bs e = do
  (phi, ts) <- inferMutrec bs
  (psi, t) <- locCSub phi (zip vars ts +|-^ infer e)
  return (psi <> phi, t)
  where vars = map binderVar bs

inferMutrec :: _
               => [p v (CoreExpr v)]
               -> IMonad v a (TySubst a a, [Type a])
inferMutrec defns = do
  tyVars <- takeNewVars (length defns)
  let decls = zip ids (map MFree tyVars)
  (phi, ts) <- decls +|- inferList exprs
  unifier <- unifyM $ zip ts (map phi tyVars)
  return (unifier <> phi, map (unifier <> phi) tyVars)
  where
    ids = map pFst defns
    exprs = map pSnd defns
