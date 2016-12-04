{-# LANGUAGE ScopedTypeVariables #-}

{- Pattern matching translation

   Contains code to translate expressions in the main language, which contain
   pattern matching definitions of top-level functions and let(rec) expressions,
   into Core (enritched lambda-calculus) expressions which do not.
   The translation works by translating each pattern matching into a series of
   semantically equivalent case expressions.

   TODO: explicit type annotations (especially those with scoped type variables)
   are for debugging and development aid, and most of them should be removed
   when code is sufficiently stable, to enhance readability.
-}

module Lang.PatternCompiler where

import Data.Maybe(fromMaybe, isJust)
import Control.Applicative((<|>))
import Data.Either(partitionEithers)
import Utils
import Data.Set(toList)
import Control.Arrow(second)
import Control.Monad.Reader
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

match :: forall a . (Eq a, PickFresh a)
      => [a]
      -> [Equation a]
      -> CoreExpr a
      -> PMMonad a (CoreExpr a)
match [] eqs def | allEmptyPatterns eqs = emptyRule eqs def
                 | otherwise = error "failed"
match (u:us) eqs defExpr
  | allStartWithVar eqs
  = varRule (u :| us) eqs defExpr
  | otherwise = ((allStartWithCtor eqs >>= Just . ctorRule (u :| us) defExpr)
            <|> ( allStartWithNum  eqs >>= Just . numRule  (u :| us) defExpr))
            `fromMaybe'` mixtureRule (u : us) eqs defExpr

--------------------------------------------------------------------------------
-- Pattern-matching let(rec)s

matchLetBinders :: (Show a, Eq a, PickFresh a)
                => [(Pattern a, CoreExpr a)]
                -> PMMonad a [(a, CoreExpr a)]
matchLetBinders b = ((varPs ++) . join) <$> forM nonVarPs matchBind
  where
    (varPs, nonVarPs) = partitionEithers (map decideVar b)
    decideVar :: (Pattern a, CoreExpr a)
              -> Either (a, CoreExpr a) (Pattern a, CoreExpr a)
    decideVar (PVar x, e) = Left (x, e)
    decideVar (PInt p, e) = Right (PInt p, e)
    decideVar (PCtor p1 p2, e) = Right (PCtor p1 p2, e)

matchBind :: forall a . (Show a, Eq a, PickFresh a)
          => (Pattern a, CoreExpr a)
          -> PMMonad a [(a, CoreExpr a)]
matchBind (p, m) =
  forM patternVars (getBinderForSinglePatternVariable p m)
  where
    patternVars :: [a]
    patternVars = patternFreeVars p
    getBinderForSinglePatternVariable :: Pattern a
                                      -> CoreExpr a
                                      -> a
                                      -> PMMonad a (a, CoreExpr a)
    getBinderForSinglePatternVariable pp scrutinee x = do
      v <- head <$> pickNFresh 1
      e <- match [v] [([pp], EVar x)] EError
      case e of
        (ECase _ a) -> return (x, ECase scrutinee a)
        _ -> error $ "this was found: " ++ show e

--------------------------------------------------------------------------------
-- Numeric literals rule

numRule :: forall a . (Eq a, PickFresh a)
        => NonEmpty a
        -> CoreExpr a
        -> [(Int, Equation a)]
        -> PMMonad a (CoreExpr a)
numRule (u :| us) defExpr = foldr folder (return defExpr)
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
  let decl = wantedDataDecl decls
  return $ map ctorDeclToPair (Data.List.NonEmpty.toList . snd $ decl)
  where
    hasDataCtor :: CtorName -> DataDecl -> Bool
    hasDataCtor dataCtor (_,dataCtors) =
      dataCtor `elem` map fst (Data.List.NonEmpty.toList dataCtors)
    hasDataCtors :: [CtorName] -> DataDecl -> Bool
    hasDataCtors ctors datadecl = all (`hasDataCtor` datadecl) ctors
    wantedDataDecl decls = head $ filter (hasDataCtors names) decls
    ctorDeclToPair :: CtorDecl -> (CtorName, CtorArity)
    ctorDeclToPair (name, names) = (name, length names - 1)

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

ctorRule :: forall a . (Eq a, PickFresh a)
         => NonEmpty a
         -> CoreExpr a
         -> [CtorEquation a]
         -> PMMonad a (CoreExpr a)
ctorRule (u :| us) defaultExpr ctorEqs =
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
mixtureRule us eqs defaultExpr =
  foldr folder (return defaultExpr) (chunkBy eqEquality eqs)
  where
    folder :: [Equation a] -> PMMonad a (CoreExpr a) -> PMMonad a (CoreExpr a)
    folder eq st = st >>= match us eq

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
