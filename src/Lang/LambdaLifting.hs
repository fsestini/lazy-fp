{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# OPTIONS_GHC -Wall #-}

module Lang.LambdaLifting (liftSupercombinators, PickNew) where

import Control.Monad.State.Lazy
import Data.Maybe (listToMaybe)
import Data.List (sortBy)
import Lang.Syntax
import Control.Monad.Reader
import Control.Arrow (second)

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
-- Auxiliary stack data structure and other utilities

type Stack a = [a]

push :: a -> Stack a -> Stack a
push x st = x : st

search :: (a -> Bool) -> Stack a -> a
search _ [] = error "not found"
search p (x : xs) | p x = x
                  | otherwise = search p xs

fixpoint :: Eq a => a -> (a -> a) -> a
fixpoint x f = let y = f x in if x == y then x else fixpoint y f

fstOf3 :: (a,b,c) -> a
fstOf3 (x,_,_) = x

thirdOf3 :: (a,b,c) -> c
thirdOf3 (_,_,x) = x

third :: (c -> d) -> (a, b, c) -> (a, b, d)
third f (x,y,z) = (x,y,f z)

second' :: (b -> b -> c) -> (a,b) -> (a,b) -> c
second' f (_,i) (_,j) = f i j

secondM :: Monad m => (b -> m d) -> (a,b) -> m (a,d)
secondM f (x,y) = (,) x <$> f y

thirdM :: Monad m => (c -> m d) -> (a,b,c) -> m (a,b,d)
thirdM f (x,y,z) = (,,) x y <$> f z

--------------------------------------------------------------------------------
-- Annotation of abstract syntax trees with binding levels

data AnnotatedExpr a = AEScName a
                     | AEBound a Int
                     | AENum Int
                     | AECtor CtorName
                     | AEAp (AnnotatedExpr a) (AnnotatedExpr a)
                     | AELet LetMode [(a, AnnotatedExpr a)] (AnnotatedExpr a)
                     | AECase (AnnotatedExpr a) [AnnotatedAlter a]
                     | AELam a (AnnotatedExpr a)
                     | AEPrimitive PrimOp
                     deriving (Eq, Show)

data AnnotEnv a = AnnotEnv { stack :: Stack (BindingInfo a)
                           , currentLevel :: Int
                           , scNames :: [a] }

type AnnotatedAlter a = (CtorName, [a], AnnotatedExpr a)
type AScDefn a = (a, [a], AnnotatedExpr a)
type BindingInfo a = (a, Int)

freeVars :: Eq a => AnnotatedExpr a -> [(a,Int)]
freeVars (AEBound x i) = [(x,i)]
freeVars (AEAp e1 e2) = freeVars e1 ++ freeVars e2
freeVars (AELam x e) = filter (\(y,_) -> x /= y) $ freeVars e
freeVars (AELet _ b e) =
  freeVars e ++ concatMap (freeVars . snd) b
freeVars (AECase e alters) =
    freeVars e ++ concatMap (freeVars . thirdOf3) alters
freeVars _ = []

shiftPushSymbols :: [a] -> AnnotEnv a -> AnnotEnv a
shiftPushSymbols symbols env = env { currentLevel = level + 1
                                   , stack = foldr push (stack env) toPush }
  where level = currentLevel env
        toPush = map (\x -> (x, level + 1)) symbols

pushSymbols :: [a] -> AnnotEnv a -> AnnotEnv a
pushSymbols symbols env = env { stack = foldr push (stack env) toPush }
  where level = currentLevel env
        toPush = map (\x -> (x, level)) symbols

annotate :: Eq a => Expr a -> Reader (AnnotEnv a) (AnnotatedExpr a)
annotate (EVar x) = do
  env <- ask
  if x `elem` scNames env
    then return $ AEScName x
    else let (_,l) = search ((== x) . fst) (stack env) in return $ AEBound x l
annotate (ENum n) = return $ AENum n
annotate (ECtor name) = return $ AECtor name
annotate (EAp e1 e2) = AEAp <$> annotate e1 <*> annotate e2
annotate (ELam x e) = AELam x <$> local (shiftPushSymbols [x]) (annotate e)
annotate (ELet NonRecursive bindings e) = AELet NonRecursive
  <$> forM bindings (secondM annotate)
  <*> local (shiftPushSymbols (map fst bindings)) (annotate e)
annotate (ELet Recursive bindings e) = AELet Recursive
  <$> forM bindings annotBinder
  <*> local (shiftPushSymbols (map fst bindings)) (annotate e)
  where annotBinder =
          secondM $ local (pushSymbols (map fst bindings)) . annotate
annotate (ECase e alters) = AECase <$> annotate e <*> forM alters annotAlter
  where annotAlter (name,vars,e') =
         (,,) name vars <$> local (shiftPushSymbols vars) (annotate e')
annotate (EPrimitive prim) = return $ AEPrimitive prim

deannotate :: AnnotatedExpr a -> Expr a
deannotate (AEScName name) = EVar name
deannotate (AEBound x _) = EVar x
deannotate (AENum n) = ENum n
deannotate (AECtor name) = ECtor name
deannotate (AEAp aexpr1 aexpr2) = EAp (deannotate aexpr1)
                                      (deannotate aexpr2)
deannotate (AELet m b e) = ELet m (map (second deannotate) b)
                                  (deannotate e)
deannotate (AECase e alters) =
  ECase (deannotate e) (map (third deannotate) alters)
deannotate (AELam x e) = ELam x (deannotate e)
deannotate (AEPrimitive p) = EPrimitive p

annotateSc :: Eq a => [a] -> ScDefn a -> AScDefn a
annotateSc names (name,vars,e) = (name, vars, runReader (annotate e) env)
  where env = AnnotEnv (zip vars [1..]) (length vars) names

deannotateSc :: AScDefn a -> ScDefn a
deannotateSc = third deannotate

annotateSupercombinators :: Eq a => [ScDefn a] -> [AScDefn a]
annotateSupercombinators scs = map (annotateSc (map fstOf3 scs)) scs

deannotateSupercombinators :: [AScDefn a] -> [ScDefn a]
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

hasAbstractions :: AnnotatedExpr a -> Bool
hasAbstractions (AELam _ _) = True
hasAbstractions (AEAp e1 e2) = hasAbstractions e1 || hasAbstractions e2
hasAbstractions (AELet _ bindings e) =
  or $ hasAbstractions e : map (hasAbstractions . snd) bindings
hasAbstractions (AECase e alters) =
    or $ hasAbstractions e : map (hasAbstractions . thirdOf3) alters
hasAbstractions _ = False

type LiftMonad a b = ReaderT [a] (State [AScDefn a]) b

lambdaLift :: (Eq a, PickNew a) =>
  AnnotatedExpr a -> LiftMonad a (AnnotatedExpr a)
lambdaLift (AEAp e1 e2) = AEAp <$> lambdaLift e1 <*> lambdaLift e2
lambdaLift (AELet x b e) =
  AELet x <$> forM b (secondM lambdaLift) <*> lambdaLift e
lambdaLift (AECase e alters) =
  AECase <$> lambdaLift e <*> forM alters (thirdM lambdaLift)
lambdaLift e@(AELam x body)
  | hasAbstractions body = AELam x <$> lambdaLift body
  | otherwise = do
      nms <- ask
      scDefns <- lift get
      let names = nms ++ map fstOf3 scDefns
          frees = freeVars e
          sorted = sortBy (second' compare) frees
          name = pickNew names
          scDef = (name, map fst sorted ++ [x], body)
          newExpr = foldl (\e' (x',i) -> AEAp e' (AEBound x' i))
                      (AEScName name) sorted
      lift $ put (scDef : scDefns)
      return newExpr
lambdaLift e = return e

stepLiftSupercombinatorBody :: (PickNew a, Eq a) =>
  a -> (AnnotatedExpr a,[AScDefn a]) -> (AnnotatedExpr a, [AScDefn a])
stepLiftSupercombinatorBody name (e,scs) = (newExpr, scs ++ newDefns)
  where names = map fstOf3
        (newExpr,newDefns) =
          runState (runReaderT (lambdaLift e) (names scs ++ [name])) []

liftSupercombinator :: (PickNew a, Eq a) =>
  AScDefn a -> [AScDefn a] -> [AScDefn a]
liftSupercombinator (name,vars,body) others =
  (name, vars, newBody) : newOthers
  where
    (newBody, newOthers) =
      fixpoint (body, others) (stepLiftSupercombinatorBody name)

stepLiftSupercombinators :: (PickNew a, Eq a) => [AScDefn a] -> [AScDefn a]
stepLiftSupercombinators scs = case pickNonLifted scs of
  Nothing -> scs
  Just sc -> let others = filter (/= sc) scs
             in liftSupercombinator sc others
  where
    pickNonLifted scs' = listToMaybe $ filter (hasAbstractions . thirdOf3) scs'

liftAnnotatedSupercombinators :: (PickNew a, Eq a) => [AScDefn a] -> [AScDefn a]
liftAnnotatedSupercombinators scs = fixpoint scs stepLiftSupercombinators

--------------------------------------------------------------------------------
-- Eta-reduction of supercombinator definitions

stepEtaReduce :: Eq a => AScDefn a -> AScDefn a
stepEtaReduce def@(name, vars@(_:_), AEAp e1 (AEBound x _)) =
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

substituteScName :: Eq a => AnnotatedExpr a -> SubstEnv a (AnnotatedExpr a)
substituteScName (AEScName n) = do
  (lhs,rhs) <- ask
  if lhs == n then return $ AEScName rhs else return $ AEScName n
substituteScName (AEAp e1 e2) =
  AEAp <$> substituteScName e1 <*> substituteScName e2
substituteScName (AELam x e) = AELam x <$> substituteScName e
substituteScName (AELet m b e) =
  AELet m <$> forM b (secondM substituteScName) <*> substituteScName e
substituteScName (AECase e a) = undefined
  AECase <$> substituteScName e <*> forM a (thirdM substituteScName)
substituteScName e = return e

applyScSubstitution :: Eq a => [AScDefn a] -> SubstEnv a [AScDefn a]
applyScSubstitution = mapM subst
  where
    subst (name,v,e) = (do
      (lhs,rhs) <- ask
      if name == lhs then return $ (,,) rhs v else return $ (,,) name v)
      <*> substituteScName e

--------------------------------------------------------------------------------
-- Main function

-- Performs lambda-lifting of a group of supercombinators, returning a new
-- group in which no supercombinator has lambda abstractions in their bodies.
-- It takes as parameter the identifier of the main supercombinator, so that it
-- does not get replaced during eta reduction.
liftSupercombinators :: (Eq a, PickNew a) => a -> [ScDefn a] -> [ScDefn a]
liftSupercombinators main = deannotateSupercombinators
  . etaReduceSupercombinators main
  . liftAnnotatedSupercombinators
  . annotateSupercombinators
