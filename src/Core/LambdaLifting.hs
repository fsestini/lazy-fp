{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts,
             LambdaCase, PatternSynonyms, TypeOperators, TypeSynonymInstances,
             FlexibleInstances, TemplateHaskell #-}

module Core.LambdaLifting --(liftSupercombinators, PickNew)
  where

import Data.Foldable
import qualified Data.Set as S
import qualified Data.List.NonEmpty as NE
import Data.Bifunctor
import Data.Bifunctor.TH
import Data.Bifoldable
import Data.Bitraversable
import AST
import RecursionSchemes
import Utils
import Control.Monad.State.Lazy
import Data.Maybe (listToMaybe)
import Data.List (sortBy)
import Core.Syntax
import Control.Monad.Reader
import Core.CaseStripping
import GMachine.Syntax

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
1. the level of a lambda abstraction is one more than the number of lambda abstractions which textually enclose it. Id there is node, then its level is 1.
2. The level of a variable is the level of the lambda abstraction that binds it
3. the level of a constant is 0

Now to maximize the chances of being able to apply eta-reduction we can simply sort the extra parameters in increasing order of lexical level.

-}

--------------------------------------------------------------------------------
-- AST of the result expression

-- No-Lambda expressions
newtype NLExprBase a b = NLEB ((
    VarB :++: CtorB :++: LitB :++: AppB :++: LetB
    :++: PrimB :++: ErrB :++: GSelB :++: GCaseB
  ) a b) deriving (Eq)

type NLExpr = FixB NLExprBase

--------------------------------------------------------------------------------
-- Auxiliary stack data structure and other utilities

type Stack a = [a]

push :: a -> Stack a -> Stack a
push x st = x : st

search :: (a -> Bool) -> Stack a -> a
search _ [] = error "not found"
search p (x : xs) | p x = x
                  | otherwise = search p xs

--------------------------------------------------------------------------------
-- Annotation of abstract syntax trees with binding levels

data ScNameB a b = ScNameB a deriving (Eq, Ord, Show)
$(deriveBifunctor ''ScNameB)
$(deriveBifoldable ''ScNameB)
$(deriveBitraversable ''ScNameB)

data BoundB a b = BoundB a Int deriving (Eq, Ord, Show)
$(deriveBifunctor ''BoundB)
$(deriveBifoldable ''BoundB)
$(deriveBitraversable ''BoundB)

newtype AnnotatedB a b = AB (
  (BoundB :++: CtorB :++: LitB :++: AppB :++: LetB
  :++: CaseB :++: LamB :++: PrimB :++: ErrB :++: ScNameB) a b)
  deriving (Bifunctor, Bifoldable, Eq, Ord, Show)

instance Bitraversable AnnotatedB where
  bitraverse f g (AB t) = AB <$> bitraverse f g t

type Annotated = FixB AnnotatedB

instance (Eq a) => Eq (Annotated a) where
  (FixB e1) == (FixB e2) = e1 == e2

data AnnotEnv a = AnnotEnv { stack :: Stack (BindingInfo a)
                           , currentLevel :: Int
                           , scNames :: [a] }

type AnnotatedAlter a = AnnotatedB a (Annotated a)
type AScDefn a = (a, [a], Annotated a)
type BindingInfo a = (a, Int)

aFreeVars :: Ord a => Annotated a -> S.Set (BindingInfo a)
aFreeVars = cata $ \case
  (BoundFA x i) -> S.singleton (x,i)
  (AppFA e1 e2) -> e1 `S.union` e2
  (LamFA x e) -> e `S.difference` S.singleton (x,0)
  (LetFA m b e) -> (e `S.difference` lhss) `S.union`
                   (rhsFreeVars `S.difference` recNonRec m lhss S.empty)
    where
      lhss = fromFoldable $ NE.map (\b -> (binderVar b,0)) b
      rhsFreeVars = foldr S.union S.empty (NE.map binderBody b)
  (CaseFA e a) -> e `S.union` foldr S.union S.empty (NE.map alterFreeVars a)
    where
      alterFreeVars (AlterB _ vars e) =
        e `S.difference` (S.fromList . map (\x -> (x,0)) $ vars)
  _ -> S.empty

shiftPushSymbols :: [a] -> AnnotEnv a -> AnnotEnv a
shiftPushSymbols symbols env = env { currentLevel = level + 1
                                   , stack = foldr push (stack env) toPush }
  where level = currentLevel env
        toPush = map (\x -> (x, level + 1)) symbols

pushSymbols :: [a] -> AnnotEnv a -> AnnotEnv a
pushSymbols symbols env = env { stack = foldr push (stack env) toPush }
  where level = currentLevel env
        toPush = map (\x -> (x, level)) symbols

annotate :: Eq a => CoreExpr a -> Reader (AnnotEnv a) (Annotated a)
annotate = cata $ \case
  (EVarF x) -> do
    env <- ask
    if x `elem` scNames env
      then return $ AEScName x
      else let (_,l) = search ((== x) . fst) (stack env) in return $ AEBound x l
  (ELamF x e) -> AELam x <$> local (shiftPushSymbols [x]) e
  (ELetF m b e) -> AELet m <$> b' <*> pusher e
    where symbols = NE.toList . NE.map binderVar $ b
          b' = forM b (sequenceA . second pusher)
          pusher = local (shiftPushSymbols symbols)
  (ECaseF e a) -> AECase <$> e <*> forM a annotAlter
    where annotAlter (AlterB name vars e') =
            AlterB name vars <$> local (shiftPushSymbols vars) e'
  (ELitFB e)  -> seqfix . AB . inj $ e
  (ECtorFB e) -> seqfix . AB . inj $ e
  (EAppFB e)  -> seqfix . AB . inj $ e
  (EPrimFB e) -> seqfix . AB . inj $ e

deannotate :: Annotated a -> CoreExpr a
deannotate = cata $ \case
  (ScNameFA name) -> EVar name
  (BoundFA x _) -> EVar x
  (CtorFAB e)   -> FixB . CEB $ inj e
  (LitFAB e)    -> FixB . CEB $ inj e
  (AppFAB e)    -> FixB . CEB $ inj e
  (LetFAB e)    -> FixB . CEB $ inj e
  (CaseFAB e)   -> FixB . CEB $ inj e
  (LamFAB e)    -> FixB . CEB $ inj e
  (PrimFAB e)   -> FixB . CEB $ inj e
  (ErrFAB e)    -> FixB . CEB $ inj e

annotateSc :: Eq a => [a] -> CoreScDefn a -> AScDefn a
annotateSc names (name,vars,e) = (name, vars, runReader (annotate e) env)
  where env = AnnotEnv (zip vars [1..]) (length vars) names

deannotateSc :: AScDefn a -> CoreScDefn a
deannotateSc = third deannotate

annotateSupercombinators :: Eq a => [CoreScDefn a] -> [AScDefn a]
annotateSupercombinators scs = map (annotateSc (map fstOf3 scs)) scs

deannotateSupercombinators :: [AScDefn a] -> [CoreScDefn a]
deannotateSupercombinators = map deannotateSc

--------------------------------------------------------------------------------
-- Lambda lifting

class PickNew a where
  pickNew :: [a] -> a

instance PickNew Name where
  pickNew [] = "X"
  pickNew names = longest ++ "1"
    where maxLen = maximum (map length names)
          longest = head $ filter (\name -> length name == maxLen) names

hasAbstractions :: Annotated a -> Bool
hasAbstractions = cata $ \case
  (LamFA _ _) -> True
  (BoundFA _ _) -> False
  (CtorFA _) -> False
  (LitFA _) -> False
  (PrimFA _) -> False
  ErrFA -> False
  (ScNameFA _) -> False
  e -> or e

type LiftMonad a b = ReaderT [a] (State [AScDefn a]) b

lambdaLift :: (Ord a, PickNew a) => Annotated a -> LiftMonad a (Annotated a)
lambdaLift = para $ \case
  (LamFA x (body,r)) | (not . hasAbstractions) body -> do
    nms <- ask
    scDefns <- lift get
    let names = nms ++ map fstOf3 scDefns
        -- TODO check if i'm picking the right frees
        frees = aFreeVars (AELam x body)
        sorted = sortBy (second' compare) . S.toList $ frees
        name = pickNew names
        scDef = (name, map fst sorted ++ [x], body)
        newExpr = foldl (\e' (x',i) -> AEApp e' (AEBound x' i))
                    (AEScName name) sorted
    lift $ put (scDef : scDefns)
    return newExpr
  e -> seqfix . fmap snd $ e

stepLiftSupercombinatorBody :: (PickNew a, Ord a) =>
  a -> (Annotated a,[AScDefn a]) -> (Annotated a, [AScDefn a])
stepLiftSupercombinatorBody name (e,scs) = (newExpr, scs ++ newDefns)
  where names = map fstOf3
        (newExpr,newDefns) =
          runState (runReaderT (lambdaLift e) (names scs ++ [name])) []

liftSupercombinator :: (PickNew a, Ord a) =>
  AScDefn a -> [AScDefn a] -> [AScDefn a]
liftSupercombinator (name,vars,body) others =
  (name, vars, newBody) : newOthers
  where
    (newBody, newOthers) =
      fixpoint (body, others) (stepLiftSupercombinatorBody name)

stepLiftSupercombinators :: (PickNew a, Ord a) => [AScDefn a] -> [AScDefn a]
stepLiftSupercombinators scs = case pickNonLifted scs of
  Nothing -> scs
  Just sc -> let others = filter (/= sc) scs
             in liftSupercombinator sc others
  where
    pickNonLifted scs' = listToMaybe $ filter (hasAbstractions . thirdOf3) scs'

liftAnnotatedSupercombinators :: (PickNew a, Ord a)
                              => [AScDefn a] -> [AScDefn a]
liftAnnotatedSupercombinators scs = fixpoint scs stepLiftSupercombinators

--------------------------------------------------------------------------------
-- Eta-reduction of supercombinator definitions

stepEtaReduce :: Eq a => AScDefn a -> AScDefn a
stepEtaReduce def@(name, vars@(_:_), AEApp e1 (AEBound x _)) =
  if lastVar == x
    then (name, init vars, e1)
    else def
  where lastVar = last vars
stepEtaReduce def = def

etaReduce :: Eq a => AScDefn a -> AScDefn a
etaReduce = flip fixpoint stepEtaReduce

etaReduceSupercombinators :: Eq a => a -> [AScDefn a] -> [AScDefn a]
etaReduceSupercombinators main scs = filter (not . strictIdFilter) $
  foldr folder etaReduced identities
  where etaReduced = map etaReduce scs
        filtered = filter idFilter etaReduced
        identities = filter ((/= main) . fst) $
          map (\(n,_,AEScName m) -> (n,m)) filtered
        idFilter (_, [], AEScName _) = True
        idFilter _ = False
        strictIdFilter (name, [], AEScName name') = name == name'
        strictIdFilter _ = False
        folder p list = runReader (applyScSubstitution list) p

type SubstEnv a b = Reader (a,a) b

substituteScName :: Eq a => Annotated a -> SubstEnv a (Annotated a)
substituteScName = cata $ \case
  (ScNameFA n) -> do
    (lhs,rhs) <- ask
    if lhs == n then return $ AEScName rhs else return $ AEScName n
  e -> seqfix e

applyScSubstitution :: Eq a => [AScDefn a] -> SubstEnv a [AScDefn a]
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
liftSupercombinators :: (Ord a, PickNew a)
                     => a
                     -> [CoreScDefn a]
                     -> [CoreScDefn a]
liftSupercombinators main = deannotateSupercombinators
  . etaReduceSupercombinators main
  . liftAnnotatedSupercombinators
  . annotateSupercombinators

--------------------------------------------------------------------------------
-- Pattern declarations

pattern BoundFA x i = (AB (Lb (BoundB x i)))
pattern CtorFA e = (AB (Rb (Lb (CtorB e))))
pattern LitFA e = (AB (Rb (Rb (Lb (LitB e)))))
pattern AppFA e1 e2 = (AB (Rb (Rb (Rb (Lb (AppB e1 e2))))))
pattern LetFA e1 e2 e3 = (AB (Rb (Rb (Rb (Rb (Lb (LetB e1 e2 e3)))))))
pattern CaseFA e1 e2 = (AB (Rb (Rb (Rb (Rb (Rb (Lb (CaseB e1 e2))))))))
pattern LamFA e1 e2 = (AB (Rb (Rb (Rb (Rb (Rb (Rb (Lb (LamB e1 e2)))))))))
pattern PrimFA e = (AB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Lb (PrimB e))))))))))
pattern ErrFA    = (AB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Lb ErrB))))))))))
pattern ScNameFA n =
  (AB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Rb (ScNameB n)))))))))))

pattern BoundFAB e = (AB (Lb e))
pattern CtorFAB e = (AB (Rb (Lb e)))
pattern LitFAB e = (AB (Rb (Rb (Lb e))))
pattern AppFAB e = (AB (Rb (Rb (Rb (Lb e)))))
pattern LetFAB e = (AB (Rb (Rb (Rb (Rb (Lb e))))))
pattern CaseFAB e = (AB (Rb (Rb (Rb (Rb (Rb (Lb e)))))))
pattern LamFAB e = (AB (Rb (Rb (Rb (Rb (Rb (Rb (Lb e))))))))
pattern PrimFAB e = (AB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Lb e)))))))))
pattern ErrFAB e  = (AB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Lb e))))))))))
pattern ScNameFAB e = (AB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Rb e))))))))))

pattern AEBound x i = (FixB (AB (Lb (BoundB x i))))
pattern AECtor e = (FixB (AB (Rb (Lb (CtorB e)))))
pattern AELit e = (FixB (AB (Rb (Rb (Lb (LitB e))))))
pattern AEApp e1 e2 = (FixB (AB (Rb (Rb (Rb (Lb (AppB e1 e2)))))))
pattern AELet e1 e2 e3 = (FixB (AB (Rb (Rb (Rb (Rb (Lb (LetB e1 e2 e3))))))))
pattern AECase e1 e2 = (FixB (AB (Rb (Rb (Rb (Rb (Rb (Lb (CaseB e1 e2)))))))))
pattern AELam e1 e2 =
  (FixB (AB (Rb (Rb (Rb (Rb (Rb (Rb (Lb (LamB e1 e2))))))))))
pattern AEPrim e = (FixB (AB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Lb (PrimB e)))))))))))
pattern AEErr    = (FixB (AB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Lb ErrB)))))))))))
pattern AEScName n =
  (FixB (AB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Rb (ScNameB n))))))))))))

--------------------------------------------------------------------------------
-- Patterns for NLExpr

pattern NLVar e = (FixB (NLEB (Lb (VarB e))))
pattern NLCtor e = (FixB (NLEB (Rb (Lb (CtorB e)))))
pattern NLLit e = (FixB (NLEB (Rb (Rb (Lb (LitB e))))))
pattern NLApp e1 e2 = (FixB (NLEB (Rb (Rb (Rb (Lb (AppB e1 e2)))))))
pattern NLLet e1 e2 e3 = (FixB (NLEB (Rb (Rb (Rb (Rb (Lb (LetB e1 e2 e3))))))))
pattern NLPrim e = (FixB (NLEB (Rb (Rb (Rb (Rb (Rb (Lb (PrimB e)))))))))
pattern NLErr = (FixB (NLEB (Rb (Rb (Rb (Rb (Rb (Rb (Lb ErrB)))))))))
pattern NLSel e1 e2 =
  (FixB (NLEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Lb (GSelB e1 e2)))))))))))
pattern NLGCase e =
  (FixB (NLEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Rb (GCaseB e)))))))))))
