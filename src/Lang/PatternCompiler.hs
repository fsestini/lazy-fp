{-# LANGUAGE ScopedTypeVariables #-}

module Lang.PatternCompiler where

import Utils
import Data.Set(toList)
import Control.Arrow(second)
import Control.Monad.Reader
import Data.Maybe(isJust)
import Control.Monad.State
import Data.List.NonEmpty(toList, NonEmpty(..))
import Control.Monad(forM)
import Lang.Syntax
import Core.Syntax
import Data.List(nubBy)
import PickFresh

type Equation a = ([Pattern a], CoreExpr a)
type PMMonad v a = ReaderT [DataDecl] (State [v]) a

pickNFresh :: PickFresh v => Int -> PMMonad v [v]
pickNFresh n = do
  soFar <- get
  let newVars = take n $ freshStream soFar
  put $ soFar ++ newVars
  return newVars

--------------------------------------------------------------------------------
-- Main function

-- Translate a single supercombinator, given by a list of pattern-matched
-- definitions.
translateSc :: forall a . (Ord a, PickFresh a)
            => [DataDecl]
            -> [([Pattern a], LangExpr a)]
            -> CoreExpr a
translateSc decls things = evalState (runReaderT monad decls) totalFreeVars
  where
    monad = do
      lambdaVars <- pickNFresh noOfPatterns
      matched <- match lambdaVars translated EError
      return $ foldr ELam matched lambdaVars
    noOfPatterns = length . fst . head $ things
    translated :: [Equation a]
    translated = map (second translateToCore) things
    allPatterns :: [Pattern a]
    allPatterns = concatMap fst things
    allExprs :: [CoreExpr a]
    allExprs = map snd translated
    totalFreeVars = concatMap patternFreeVars allPatterns
                 ++ concatMap (Data.Set.toList . allVars) allExprs

match :: (Eq a, PickFresh a)
      => [a]
      -> [Equation a]
      -> CoreExpr a
      -> PMMonad a (CoreExpr a)
match [] eqs def | allEmptyPatterns eqs = emptyRule eqs def
                 | otherwise = error "failed"
match (u:us) eqs defaultExpr
  | allStartWithVar eqs
  = varRule (u :| us) eqs defaultExpr
  | otherwise = case allStartWithCtor eqs of
      Just ctorEqs -> ctorRule (u :| us) eqs ctorEqs defaultExpr
      Nothing -> case allStartWithNum eqs of
        Just numEqs -> numRule (u :| us) numEqs defaultExpr
        Nothing -> mixtureRule (u : us) eqs defaultExpr

--------------------------------------------------------------------------------
-- Numeric literals rule

numRule :: forall a . (Eq a, PickFresh a)
        => NonEmpty a
        -> [(Int, Equation a)]
        -> CoreExpr a
        -> PMMonad a (CoreExpr a)
numRule (u :| us) eqs defExpr =
  foldr folder (return defExpr) eqs
  where
    folder :: (Int, Equation a)
           -> PMMonad a (CoreExpr a)
           -> PMMonad a (CoreExpr a)
    folder (n,eq) m = do
      trueExpr <- match us [eq] defExpr
      falseExpr <- m
      let trueAlt = ("True", [], trueExpr)
          falseAlt = ("False", [], falseExpr)
          scrutinee = EPrimitive Eql `EAp` EVar u `EAp` ENum n
      return $ ECase scrutinee (trueAlt :| [falseAlt])

startsWithNum :: Equation a -> Bool
startsWithNum (PInt _:_,_) = True
startsWithNum _ = False

allStartWithNum :: [Equation a] -> Maybe [(Int, Equation a)]
allStartWithNum eqs = if all startsWithNum eqs
  then Just $ stripLeadingNumbers eqs
  else Nothing
  where
    stripLeadingNumber (PInt n : ps, e) = (n, (ps, e))
    stripLeadingNumbers = map stripLeadingNumber

--------------------------------------------------------------------------------
-- Variables rule

stripFirstVarInEquations :: forall a . [Equation a] -> ([a], [Equation a])
stripFirstVarInEquations eqs = (map fst mapped, map snd mapped)
  where
    stripFirstVarInEquation :: Equation a -> (a, Equation a)
    stripFirstVarInEquation (PVar x : ps, e) = (x, (ps, e))
    mapped = map stripFirstVarInEquation eqs

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
        -> PMMonad a (CoreExpr a)
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

allCtorsOfDataType :: [CtorName] -> PMMonad v [(CtorName, CtorArity)]
allCtorsOfDataType names = do
  decls <- ask
  return $ group decls
  where
    group decls = head $ flip filter (map termConstructors decls) $ \gr ->
      all (`elem` map fst gr) names

ctorArity :: CtorName -> PMMonad v Int
ctorArity name = do
  decls <- ask
  let x = concatMap (Data.List.NonEmpty.toList . snd) decls
      y = head $ filter ((== name) . fst) x
  return $ (length . snd $ y) - 1

getMissingCtors :: [CtorName] -> PMMonad v [(CtorName, CtorArity)]
getMissingCtors names = do
  allOfThem <- allCtorsOfDataType names
  return $ filter ((`notElem` names) . fst) allOfThem

toAnon :: CtorEquation a -> AnonCtorEquation a
toAnon ((name, ps), ps', e) = (ps, ps', e)

ctorName :: CtorEquation a -> CtorName
ctorName ((name,_),_,_) = name

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
         -> PMMonad a (CoreExpr a)
ctorRule (u :| us) eqs ctorEqs defaultExpr =
  ECase (EVar u) <$> fmap (\(x:xs) -> x :| xs) allAlters   -- TODO: fix this
  where
    groups = groupByCtor ctorEqs
    definedAlters = mapM (groupToAlter us defaultExpr) groups
    presentCtors = map ctorName ctorEqs
    missingAlters = do
      missingCtors <- getMissingCtors presentCtors
      forM missingCtors $ \(name, arity) -> do
        newVars <- pickNFresh arity
        (,,) name newVars <$> match [] [] defaultExpr
    allAlters = (++) <$> definedAlters <*> missingAlters

groupToAlter :: (Eq a, PickFresh a)
             => [a]
             -> CoreExpr a
             -> (CtorName, [AnonCtorEquation a])
             -> PMMonad a (CoreAlter a)
groupToAlter us defaultExpr (name, eqs) = do
  arity <- ctorArity name
  newVars <- pickNFresh arity
  let newGroupOfVars = newVars ++ us
      anonToEquation (ps,ps',e) = (ps ++ ps', e)
      qs = map anonToEquation eqs
  (,,) name newVars <$> match newGroupOfVars qs defaultExpr

--------------------------------------------------------------------------------
-- Empty rule

hasEmptyPatterns :: Equation a -> Bool
hasEmptyPatterns ([],_) = True
hasEmptyPatterns _ = False

allEmptyPatterns :: [Equation a] -> Bool
allEmptyPatterns = all hasEmptyPatterns

emptyRule :: forall a . [Equation a] -> CoreExpr a -> PMMonad a (CoreExpr a)
emptyRule eqs defaultExpr = return $ head $ map snd eqs ++ [defaultExpr]

--------------------------------------------------------------------------------
-- Mixture rule

mixtureRule :: forall a . (Eq a, PickFresh a)
            => [a]
            -> [Equation a]
            -> CoreExpr a
            -> PMMonad a (CoreExpr a)
mixtureRule us eqs defaultExpr = foldr folder (return defaultExpr) partitions
  where
    folder :: [Equation a] -> PMMonad a (CoreExpr a) -> PMMonad a (CoreExpr a)
    folder eq st = st >>= match us eq
    partitions = partitionEqs eqs
    partitionEqs :: [Equation a] -> [[Equation a]]
    partitionEqs = chunkBy eqEquality

eqEquality :: Equation a -> Equation a -> Bool
eqEquality ([]  ,_) ([]  ,_) = True
eqEquality (PVar _:_,_) (PVar _:_,_) = True
eqEquality (PInt _:_,_) (PInt _:_,_) = True
eqEquality (PCtor _ _:_,_) (PCtor _ _:_,_) = True
eqEquality _ _ = False

--------------------------------------------------------------------------------

uncurry3 :: (a -> b -> c -> d) -> (a,b,c) -> d
uncurry3 f (x,y,z) = f x y z

azd :: [a -> b] -> [a] -> [b]
azd [] xs = []
azd (f:fs) [] = []
azd (f:fs) (x:xs) = f x : azd fs xs
