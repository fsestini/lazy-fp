{-# LANGUAGE ScopedTypeVariables #-}

module Lang.PatternCompiler where

import Control.Monad.Reader
import Data.Maybe(isJust)
import Control.Monad.State
import Data.List.NonEmpty(NonEmpty(..))
import Control.Monad(forM)
import Lang.Syntax
import Core.Syntax
import Data.List(nubBy)
import PickFresh

type Equation a = ([Pattern a], CoreExpr a)
type PMState v a = ReaderT [DataDecl] (State [v]) a

pickNFresh :: PickFresh v => Int -> PMState v [v]
pickNFresh n = do
  soFar <- get
  let newVars = take n $ freshStream soFar
  put $ soFar ++ newVars
  return newVars

--------------------------------------------------------------------------------
-- Main function

match :: (Eq a, PickFresh a)
      => [a]
      -> [Equation a]
      -> CoreExpr a
      -> PMState a (CoreExpr a)
match [] eqs def | allEmptyPatterns eqs = emptyRule eqs def
                 | otherwise = error "failed"
match (u:us) eqs defaultExpr
  | allStartWithVar eqs
  = varRule (u :| us) eqs defaultExpr
  | otherwise = case allStartWithCtor eqs of
      Just ctorEqs -> ctorRule (u :| us) eqs ctorEqs defaultExpr
      Nothing -> mixtureRule (u : us) eqs defaultExpr

--------------------------------------------------------------------------------
-- Variables rule

stripFirstVarInEquations :: [Equation a] -> ([a], [Equation a])
stripFirstVarInEquations = undefined

substituteInEquation :: Eq a => a -> a -> Equation a -> Equation a
substituteInEquation u v (ps, e) = (ps, substituteVar u v e)

startsWithVar :: Equation a -> Bool
startsWithVar (PVar p : ps, _) = True
startsWithVar _                 = False

allStartWithVar :: [Equation a] -> Bool
allStartWithVar = all startsWithVar

varRule :: (Eq a, PickFresh a)
        => NonEmpty a
        -> [Equation a]
        -> CoreExpr a
        -> PMState a (CoreExpr a)
varRule (u :| us) eqs = match us newEqs
  where
    (vars, eqs') = stripFirstVarInEquations eqs
    triples = zip3 (repeat u) vars eqs'
    newEqs = azd (repeat $ uncurry3 substituteInEquation) triples

--------------------------------------------------------------------------------
-- Constructors rule

type CtorArity = Int

type CtorEquation a = ((CtorName, [Pattern a]), [Pattern a], CoreExpr a)
type AnonCtorEquation a = ([Pattern a], [Pattern a], CoreExpr a)

allCtorsOfDataType :: [CtorName] -> PMState v [(CtorName, CtorArity)]
allCtorsOfDataType names = do
  decls <- ask
  return $ group decls
  where
    group decls = head $ flip filter (map termConstructors decls) $ \gr ->
      all (`elem` map fst gr) names

getMissingCtors :: [CtorName] -> PMState v [(CtorName, CtorArity)]
getMissingCtors names = do
  allOfThem <- allCtorsOfDataType names
  return $ filter ((`notElem` names) . fst) allOfThem

toAnon :: CtorEquation a -> AnonCtorEquation a
toAnon ((name, ps), ps', e) = (ps, ps', e)

ctorName :: CtorEquation a -> CtorName
ctorName ((name,_),_,_) = name

ctorArity :: CtorName -> Int
ctorArity = undefined

startsWithCtor :: Equation a -> Maybe (CtorEquation a)
startsWithCtor ([], _) = Nothing
startsWithCtor (PCtor n ps : ps', e) = Just ((n,ps), ps', e)
startsWithCtor (PVar _ : _, _) = Nothing
startsWithCtor (PInt _ : _, _) = Nothing

allStartWithCtor :: [Equation a] -> Maybe [CtorEquation a]
allStartWithCtor eqs = forM eqs startsWithCtor

groupByCtor :: [CtorEquation a] -> [(CtorName, [AnonCtorEquation a])]
groupByCtor eqs = assocList
  where
    names = map ctorName eqs
    assocList = flip map names $ \name ->
                  (name, map toAnon $ filter ((== name) . ctorName) eqs)

ctorRule :: forall a . (Eq a, PickFresh a) => NonEmpty a
         -> [Equation a]
         -> [CtorEquation a]
         -> CoreExpr a
         -> PMState a (CoreExpr a)
ctorRule (u :| us) eqs ctorEqs defaultExpr =
  ECase (EVar u) <$> allAlters
  where
    groups = groupByCtor ctorEqs
    groupToAlter :: (CtorName, [AnonCtorEquation a]) -> PMState a (CoreAlter a)
    groupToAlter (name, eqs) = do
      newVars <- pickNFresh (ctorArity name)
      let newGroupOfVars = newVars ++ us
          anonToEquation (ps,ps',e) = (ps ++ ps', e)
          qs = map anonToEquation eqs
      (,,) name newVars <$> match newGroupOfVars qs defaultExpr
    definedAlters = mapM groupToAlter groups
    presentCtors = map ctorName ctorEqs
    missingAlters = do
      missingCtors <- getMissingCtors presentCtors
      forM missingCtors $ \(name, arity) -> do
        newVars <- pickNFresh arity
        (,,) name newVars <$> match [] [] defaultExpr
    allAlters = (++) <$> definedAlters <*> missingAlters

--------------------------------------------------------------------------------
-- Empty rule

hasEmptyPatterns :: Equation a -> Bool
hasEmptyPatterns ([],_) = True
hasEmptyPatterns _ = False

allEmptyPatterns :: [Equation a] -> Bool
allEmptyPatterns = all hasEmptyPatterns

emptyRule :: forall a . [Equation a] -> CoreExpr a -> PMState a (CoreExpr a)
emptyRule eqs defaultExpr = return $ head $ map snd eqs ++ [defaultExpr]

--------------------------------------------------------------------------------
-- Mixture rule

mixtureRule :: forall a . (Eq a, PickFresh a)
            => [a]
            -> [Equation a]
            -> CoreExpr a
            -> PMState a (CoreExpr a)
mixtureRule us eqs defaultExpr = foldr folder (return defaultExpr) partitions
  where
    folder :: [Equation a] -> PMState a (CoreExpr a) -> PMState a (CoreExpr a)
    folder eq st = st >>= match us eq
    partitions = partitionEqs eqs
    partitionEqs :: [Equation a] -> [[Equation a]]
    partitionEqs [] = error "empty list"
    partitionEqs (eq:eqs) = evalState stateObj (eq:eqs)
      where stateObj = if startsWithVar eq
                         then eatVarPatterns
                         else eatCtorPatterns
    eatVarPatterns :: State [Equation a] [[Equation a]]
    eatVarPatterns = do
      eqs <- get
      let (part, rest) = span startsWithVar eqs
      if null rest
        then return [part]
        else put rest >> (:) part <$> eatCtorPatterns
    eatCtorPatterns :: State [Equation a] [[Equation a]]
    eatCtorPatterns = do
      eqs <- get
      let (part, rest) = span (isJust . startsWithCtor) eqs
      if null rest
        then return [part]
        else put rest >> (:) part <$> eatVarPatterns

--------------------------------------------------------------------------------

{-
foreach ctor C x1 ... xn
  if C not in list already
    then add a clause C x1 ... xn -> match [] [] defaultExpr to the case expr
-}

uncurry3 :: (a -> b -> c -> d) -> (a,b,c) -> d
uncurry3 f (x,y,z) = f x y z

azd :: [a -> b] -> [a] -> [b]
azd [] xs = []
azd (f:fs) [] = []
azd (f:fs) (x:xs) = f x : azd fs xs
