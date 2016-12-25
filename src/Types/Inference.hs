{-# LANGUAGE ScopedTypeVariables, TupleSections, FlexibleContexts, PartialTypeSignatures #-}
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
import Core.DependencyAnalysis

fromDataDecls :: [DataDecl] -> Except String (DataCtors a)
fromDataDecls decls = do
  ctors <- checkReturnType decls
  return . M.fromList . fmap toType $ ctors
  where
    toType (name, types) =
      (name, SMono $ foldr1 (-->) (fmap (flip MCtor []) types))
    checkReturnType decls = join <$> forM decls checkReturnType'
      where checkReturnType' (parentType, ctors) = if all aux ctors
              then return $ NE.toList ctors
              else fail $ "data constructor of type " ++ parentType
                        ++ " must return " ++ parentType
              where aux decl = NE.last (snd decl) == parentType

inferExpr :: _ => [DataDecl] -> CoreExpr v -> Except String (Type a)
inferExpr dd e = do
  dc <- fromDataDecls dd
  snd . fst <$> runIMonad M.empty dc (freshStream []) (infer e)

-- inferMutrecDefns :: _
--                  => [DataDecl]
--                  -> [p v (CoreExpr v)]
--                  -> Except String [Type a]
-- inferMutrecDefns decls defns = do
--   dc <- fromDataDecls decls
--   snd . fst <$> runIMonad M.empty dc (freshStream []) (inferMutrec defns)

inferCoreScDefns :: forall a v . (Ord a, Ord v, Show v, PickFresh a)
                 => [DataDecl]
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
