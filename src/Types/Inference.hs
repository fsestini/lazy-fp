{-# LANGUAGE GADTs, ScopedTypeVariables, TupleSections, FlexibleContexts,
             PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Types.Inference where

import AST
import Pair
import PickFresh
import Control.Arrow(second)
import Control.Monad.Except
import Control.Category (Category(..))
import qualified Stream as SM
import qualified Data.Map as M
import qualified Data.List.NonEmpty as NE
import Types.Schemes
import Types.IMonad
import Types.DataDecl
import Types.Fin
import Core.Syntax
import Core.DependencyAnalysis
import Prelude hiding (id, (.))

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
    checkArities' (MFree _) = return ()
    checkArities' (MBound _) = return ()
    checkArities' (MCtor name tys) =
      case M.lookup name aritiesMap of
        Nothing -> throwError $ name ++ "type constructor " ++ name ++ " not in scope"
        (Just arity) -> if arity == length tys
          then forM_ tys checkArities'
          else throwError $ "type constructor " ++ name ++ " has arity "
               ++ show arity ++ ", but it was applied to "
               ++ show (length tys) ++ " types"

checkReturnType :: CtorName -> Scheme n a -> Except String ()
checkReturnType parentTyName (SForall sc) = checkReturnType parentTyName sc
checkReturnType parentTyName (SMono mono) = checkReturnType' mono
  where
    failure = throwError $ "data constructor for type " ++ parentTyName
              ++ " should return an element of type " ++ parentTyName
    checkReturnType' (MFree _) = failure
    checkReturnType' (MBound _) = failure
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

inferCoreScDefns :: forall a v . (Ord a, Ord v, Show v, PickFresh a, Show a)
                 => [DataDecl a]
                 -> [CoreScDefn v]
                 -> Except String [(CoreScDefn v, TypeScheme a)]
inferCoreScDefns decls defns = do
  dc <- fromDataDecls decls
  fst <$> runIMonad M.empty dc id (freshStream [] :: SM.Stream a) inferred
  where depAn = map (second depAnalysisTrans) defns
        classified = classifyDefns depAn
        inferred = inferClassifications classified

inferClassifications :: _
                     => [Classification v]
                     -> IMonad v a [(CoreScDefn v, TypeScheme a)]
inferClassifications []  = return []
inferClassifications (ClNonRecursive (x,e) : cls) = do
  ty <- infer e
  sc <- generalizeM ty
  ts <- pushContext x sc (inferClassifications cls)
  return $ ((x,e), sc) : ts
inferClassifications (ClRecursive pairs : cls) = do
  ts <- inferMutrec pairs
  sc <- forM ts generalizeM
  let decls = zip (map fst pairs) sc
  sc' <- decls +|-^^ inferClassifications cls
  return $ zip pairs sc ++ sc'

infer :: (Ord v, Show v, Ord a, Show a) => CoreExpr v -> IMonad v a (Type a)
infer (EVar x) = inferVar x
infer (EApp e1 e2) = inferApp e1 e2
infer (ECtor name) = inferCtor name
infer (ELit (LInt _)) = return IntTy
infer (ELet NonRecursive bs e) = inferLet (NE.toList bs) e
infer (ELet Recursive bs e) = inferLetrec (NE.toList bs) e
infer (ELam x e) = inferLambda x e
infer EErr = MFree <$> newVar
infer (EPrim Add) = return $ IntTy --> IntTy --> IntTy
infer (EPrim Sub) = return $ IntTy --> IntTy --> IntTy
infer (EPrim Mul) = return $ IntTy --> IntTy --> IntTy
infer (EPrim Eql) = return $ IntTy --> IntTy --> BoolTy
infer (ECase e a) = inferCase e a

inferCase :: _
          => CoreExpr v
          -> NE.NonEmpty (AlterB v (CoreExpr v))
          -> IMonad v a (Type a)
inferCase e a = infer e >>= inferAlters a

inferAlter :: _ => Type a -> AlterB v (CoreExpr v) -> IMonad v a (Type a)
inferAlter scrType (AlterB name vars e) = do
  freshTypeVars <- map MFree <$> takeNewVars (length vars)
  let ctxtAddition = zip vars freshTypeVars
      term = foldl EApp (ECtor name) (map EVar vars)
  t <- ctxtAddition +|- infer term
  unify [(t, scrType)]
  let newDecls = zip vars freshTypeVars
  ty <- newDecls +|- infer e
  applyCurrentSub ty

inferAlters :: _
            => NE.NonEmpty (AlterB v (CoreExpr v))
            -> Type a
            -> IMonad v a (Type a)
inferAlters a scrType = flip foldr1 (fmap (inferAlter scrType) a) $
  \ a1 a2 -> do
    t1 <- a1
    t2 <- a2
    unify [(t1, t2)]
    applyCurrentSub t2

inferCtor :: _ => CtorName -> IMonad v a (Type a)
inferCtor name = dataCtors >>= maybe (throwError errMsg) fullyInstM . M.lookup name
  where errMsg = "data constructor " ++ name ++ " not in scope"

inferVar :: _ => v -> IMonad v a (Type a)
inferVar = fullyInstM <=< schemeOfVar

inferApp :: _ => CoreExpr v -> CoreExpr v -> IMonad v a (Type a)
inferApp e1 e2 = do
  ty1 <- infer e1
  ty2 <- infer e2
  beta <- MFree <$> newVar
  unify [(ty1, ty2 --> beta)]
  return beta

inferLambda :: _ => v -> CoreExpr v -> IMonad v a (Type a)
inferLambda x e = do
  beta <- MFree <$> newVar
  ty <- pushContext x (SMono beta) (infer e)
  return $ beta --> ty

inferList :: _ => [CoreExpr v] -> IMonad v a [Type a]
inferList = mapM infer

inferLet :: _ => [BinderB v (CoreExpr v)] -> CoreExpr v -> IMonad v a (Type a)
inferLet b e = do
  ts <- inferList (map binderBody b)
  zip bVars ts +|-^ infer e
  where bVars = map binderVar b

inferLetrec :: _
            => [BinderB v (CoreExpr v)]
            -> CoreExpr v
            -> IMonad v a (Type a)
inferLetrec bs e = do
  ts <- inferMutrec bs
  zip vars ts +|-^ infer e
  where vars = map binderVar bs

inferMutrec :: _
               => [p v (CoreExpr v)]
               -> IMonad v a [Type a]
inferMutrec defns = do
  tyVars <- map MFree <$> takeNewVars (length defns)
  let decls = zip ids tyVars
  ts <- decls +|- inferList exprs
  unify $ zip ts tyVars
  return tyVars
  where
    ids = map pFst defns
    exprs = map pSnd defns
