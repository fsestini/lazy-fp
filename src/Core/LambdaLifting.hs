{-# LANGUAGE FlexibleContexts, LambdaCase, PatternSynonyms, TypeOperators,
             TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}

module Core.LambdaLifting (
    liftSupercombinators
  , NLExprBase
  , NLExpr
  , NLScDefn
  ) where

import Control.Arrow((***))
import PickFresh
import Data.Foldable
import qualified Data.Set as S
import Data.Bifunctor.TH
import AST
import Utils
import Control.Monad.State.Lazy
import Data.List (sortBy)
import Control.Monad.Reader
import Core.CaseStripping
import GMachine.Syntax
import Data.Comp.Bifun
import MonadVar

{- Lambda-lifting algorithm

Until there are no more lambda abstractions:

1. Choose any lambda abstraction which has no inner lambda abstractions in its
   body.
2. Take out all its free variables as extra parameters
3. Give an arbitrary name to the lambda abstraction
4. Replace the occurrence of the lambda abstraction by the name applied to the
   free variables
5. Compile the lambda abstraction and associate the name with the compiled code

-}

{- Optimization 1: redundant parameters

Consider \x . \y . - y x

Blindly applying the algorithm yields

$Y x y = - y x
\x . $Y x

and then

$Y x y = - y x
$X x = $Y x
$X

By eta-reduction, $X = $Y, so $X can actually be replaced with $Y everywhere:

$Y x y = - y x
$Y

So
1. Remove redundant parameters from definitions by eta-reduction
2. Where this produces redundant definitions, eliminate them

-}

{- Optimization 2: free variables ordering

We should orer the free variables, with those bound at inner levels coming last
in the parameter list of the supercombinator.

We can assign syntactic objects a lexical level as follows:
1. the level of a lambda abstraction is one more than the number of lambda abstractions which textually enclose it. If there is none, then its level is 1.
2. The level of a variable is the level of the lambda abstraction that binds it
3. the level of a constant is 0

Now to maximize the chances of being able to apply eta-reduction we can simply sort the extra parameters in increasing order of lexical level.

-}

--------------------------------------------------------------------------------
-- AST of the result expression

data Ann a b = Free | Lam Int | Let Int
type AnnVarB = VarB :*: Ann

$(deriveBifunctor ''Ann)
$(deriveBifoldable ''Ann)
$(deriveBitraversable ''Ann)

iAnnVarLam :: (AnnVarB :<: f) => a -> Int -> Term f a
iAnnVarLam x i = inject $ VarB x :*: Lam i

iAnnVarLet :: (AnnVarB :<: f) => a -> Int -> Term f a
iAnnVarLet x i = inject $ VarB x :*: Let i

iAnnVarFree :: (AnnVarB :<: f) => a -> Term f a
iAnnVarFree x = inject $ VarB x :*: Free

-- No-Lambda expressions
type NLExprBase = VarB :+: CtorB :+: LitB :+: AppB
                    :+: LetB :+: PrimB :+: ErrB :+: GSelB :+: GCaseB
type NLExpr = Term NLExprBase
type NLScDefn v = (v, [v], NLExpr v)

-- Annotated CSExpr expressions
type AnnBase = AnnVarB :+: CtorB :+: LitB :+: AppB
               :+: LetB :+: LamB :+: PrimB :+: ErrB
               :+: GSelB :+: GCaseB
type Annotated = Term AnnBase
type AScDefn a = (a, Annotated a)

--------------------------------------------------------------------------------
-- Term annotation

type VRest = LamB :+: LetB :+: CtorB :+: LitB :+: AppB :+: PrimB
            :+: ErrB :+: GSelB :+: GCaseB

annotate :: Ord a => CSExpr a -> Annotated a
annotate = runEmpty . cataM (monadVarTrans (split alg1 alg2))
  where
    alg1 (VarB x) = do
      env <- varEnv
      case lookupVarEnv x env of
        (Just (LamBound y)) -> return $ inject $ VarB x :*: Lam y
        (Just (LetBound y)) -> return $ inject $ VarB x :*: Let y
        Nothing -> return $ inject $ VarB x :*: Free
    alg2 :: VRest a (Annotated a) -> VarReader a (Annotated a)
    alg2 = return . inject

--------------------------------------------------------------------------------
-- Free lambda-bound variables

                  -- lam, let
freeNLVars :: forall a . Ord a
           => AnnNLExpr a
           -> (S.Set (a,Int), S.Set (a,Int))
freeNLVars = runEmpty . cataM (monadVarLetTrans (split alg1 alg2))
  where
    alg1 (VarB v :*: Let i) = do
      (LetLevel ll) <- letLevel :: VarReader a (LetLevel a)
      if i > ll
        then return (S.empty, S.singleton (v,i))
        else return (S.empty, S.empty)
    alg1 (VarB v :*: Lam i) = return (S.singleton (v,i), S.empty)
    alg1 _ = return (S.empty, S.empty)
    alg2 :: BareBase a (S.Set (a,Int), S.Set (a,Int))
         -> VarReader a (S.Set (a,Int), S.Set (a,Int))
    alg2 = return . foldr unioner (S.empty, S.empty)
    unioner (x,y) (z,w) = (S.union x z, S.union y w)

--------------------------------------------------------------------------------
-- Annotation of abstract syntax trees with binding levels

genDeannotate :: forall p p' q a b .
                 (p :=: AnnVarB :+: p', VarB :<: q)
              => (p' a b -> q a b) -> p a b -> q a b
genDeannotate = split vAlg
  where
    vAlg :: AnnVarB a b -> q a b
    vAlg (VarB x :*: _) = inj $ VarB x

deannotate :: AnnNLExpr a -> NLExpr a
deannotate = Term . deann . fmap deannotate . unTerm
  where deann = genDeannotate
          (inj :: BareBase a (NLExpr a) -> NLExprBase a (NLExpr a))

annotateSc :: Ord a => CSScDefn a -> AScDefn a
annotateSc (name,e) = (name, annotate e)

deannotateSc :: AnnNLScDefn a -> NLScDefn a
deannotateSc = third deannotate

annotateScs :: Ord a => [CSScDefn a] -> [AScDefn a]
annotateScs = map annotateSc

deannotateScs :: [AnnNLScDefn a] -> [NLScDefn a]
deannotateScs = map deannotateSc

--------------------------------------------------------------------------------
-- Auxiliary monad for lambda lifting

type LiftMonad a b = ReaderT [a] (State [AnnNLScDefn a]) b

runLiftMonad :: LiftMonad a b
             -> [a]
             -> [AnnNLScDefn a]
             -> (b, [AnnNLScDefn a])
runLiftMonad m = runState . runReaderT m

freshName :: PickFresh a => LiftMonad a a
freshName = do
  nms <- ask
  scDefns <- get
  let nms' = map fstOf3 scDefns
  return $ pickFresh $ nms ++ nms'

pushSc :: AnnNLScDefn a -> LiftMonad a ()
pushSc sc = do
  defns <- get
  put (sc : defns)

--------------------------------------------------------------------------------
-- Lambda lifting

type LRest = AnnVarB :+: LetB :+: CtorB :+: LitB :+: AppB :+: PrimB
            :+: ErrB :+: GSelB :+: GCaseB

type BareBase = LetB :+: CtorB :+: LitB :+: AppB :+: PrimB
              :+: ErrB :+: GSelB :+: GCaseB

type AnnNLBase = AnnVarB :+: BareBase
type AnnNLExpr = Term AnnNLBase

type AnnNLScDefn v = (v, [v], AnnNLExpr v)

sortPair :: Ord a => [(a,Int)] -> [(a,Int)]
sortPair = sortBy ordering
  where
    ordering (x,i) (y,j) = case compare i j of
      EQ -> compare x y
      z -> z

lambdaLift :: forall a . (Ord a, PickFresh a)
           => Annotated a -> LiftMonad a (AnnNLExpr a)
lambdaLift = cataM (split alg1 alg2)
  where
    alg1 :: LamB a (AnnNLExpr a) -> LiftMonad a (AnnNLExpr a)
    alg1 (LamB x e) = do
      name <- freshName
      let listSorter = reverse . sortPair . S.toList . S.insert (x,0)
          (lamVars, letVars) = listSorter *** listSorter $ freeNLVars e
          scDef = (name, map fst letVars ++ map fst lamVars, e)
          lamAnnVars = map (uncurry iAnnVarLam) lamVars
          letAnnVars = map (uncurry iAnnVarLet) letVars
          newExpr = foldl' iApp (iAnnVarFree name)
                                (letAnnVars ++ init lamAnnVars)
      pushSc scDef
      return newExpr
    alg2 :: LRest a (AnnNLExpr a) -> LiftMonad a (AnnNLExpr a)
    alg2 = return . inject

liftAScM :: (PickFresh a, Ord a)
         => AScDefn a -> LiftMonad a (AnnNLScDefn a)
liftAScM (name, body) = (name, [],) <$> lambdaLift body

liftAScsM :: (PickFresh a, Ord a)
          => [AScDefn a] -> LiftMonad a [AnnNLScDefn a]
liftAScsM = mapM liftAScM

liftAScs :: (PickFresh a, Ord a) => [AScDefn a] -> [AnnNLScDefn a]
liftAScs defns =
  uncurry (++) $ runLiftMonad (liftAScsM defns) (map fst defns) []

--------------------------------------------------------------------------------
-- Eta-reduction of supercombinator definitions

pattern NLVar :: a -> NLExpr a
pattern NLVar x = (Term (Inl (VarB x)))

pattern NLApp :: NLExpr a -> NLExpr a -> NLExpr a
pattern NLApp x1 x2 = (Term (Inr (Inr (Inr (Inl (AppB x1 x2))))))

stepEtaReduce :: Eq a => NLScDefn a -> NLScDefn a
stepEtaReduce def@(name, vars@(_:_), NLApp e (NLVar x)) =
  if last vars == x
    then (name, init vars, e)
    else def
stepEtaReduce def = def

instance Eq a => Eq (NLExpr a) where
  (Term t1) == (Term t2) = t1 == t2

etaReduce :: Eq a => NLScDefn a -> NLScDefn a
etaReduce = flip fixpoint stepEtaReduce

etaReduceScs :: Eq a => a -> [NLScDefn a] -> [NLScDefn a]
etaReduceScs main scs =
  filter (not . strictIdFilter) $ foldr folder etaReduced identities
  where etaReduced = map etaReduce scs
        filtered = filter idFilter etaReduced
        identities = filter ((/= main) . fst) $
          map (\(n, _, NLVar m) -> (n,m)) filtered
        idFilter (_, [], NLVar _) = True
        idFilter _ = False
        strictIdFilter (name, [], NLVar name') = name == name'
        strictIdFilter _ = False
        folder p list = runReader (applyScSubstitution list) p

type SubstEnv a b = Reader (a,a) b

substituteScName :: Eq a => NLExpr a -> SubstEnv a (NLExpr a)
substituteScName = cataM (split alg1 alg2)
  where
    alg1 (VarB x) = do
      (lhs, rhs) <- ask
      if lhs == x
        then return . inject $ VarB rhs
        else return . inject $ VarB x
    alg2 :: BareBase a (NLExpr a) -> SubstEnv a (NLExpr a)
    alg2 = return . inject

applyScSubstitution :: Eq a => [NLScDefn a] -> SubstEnv a [NLScDefn a]
applyScSubstitution = mapM $ \(name,v,e) -> (do
  (lhs,rhs) <- ask
  if name == lhs then return $ (,,) rhs v else return $ (,,) name v)
  <*> substituteScName e

--------------------------------------------------------------------------------
-- Main function

-- Performs lambda-lifting of a group of supercombinators, returning a new
-- group in which no supercombinator has lambda abstractions in their bodies.
-- It takes as parameter the identifier of the main supercombinator, so that it
-- does not get replaced during eta reduction.
liftSupercombinators :: (Ord a, PickFresh a)
                     => a
                     -> [CSScDefn a]
                     -> [NLScDefn a]
liftSupercombinators main =
  etaReduceScs main . deannotateScs . liftAScs . annotateScs
