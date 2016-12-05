module Core.Syntax (
  CoreExpr(..),
  CoreAlter,
  freeVars,
  allVars,
  LetMode(..),
  Name,
  CtorName
) where

import Data.Set hiding (foldr, map)
import Lang.Syntax(LangExpr(..), Lit(..), PrimOp, LetMode(..), Name, CtorName)
import Control.Arrow (second)
import qualified Data.List.NonEmpty as NE (NonEmpty(..), map, toList)
import Utils

type CoreAlter a = (CtorName, [a], CoreExpr a)
type CoreScDefn a = (a, [a], CoreExpr a)

data CoreExpr a = EVar a
            | ENum Int
            | ECtor CtorName
            | EAp (CoreExpr a) (CoreExpr a)
            | ELet LetMode (NE.NonEmpty (a, CoreExpr a)) (CoreExpr a)
            | ECase (CoreExpr a) (NE.NonEmpty (CoreAlter a))
            | ELam a (CoreExpr a)
            | EPrimitive PrimOp -- primitive operations
            | EError
            deriving (Eq, Show)

-- [u/v]e, where u is fresh
substituteVar :: Eq a => a -> a -> CoreExpr a -> CoreExpr a
substituteVar u v (EVar x) | v == x = EVar u
                           | otherwise = EVar x
substituteVar u v (EAp e1 e2) =
  EAp (substituteVar u v e1) (substituteVar u v e2)
substituteVar u v (ELet mode binds e) =
  ELet mode (NE.map (second (substituteVar u v)) binds) (substituteVar u v e)
substituteVar u v (ECase e alts) =
  ECase (substituteVar u v e) (NE.map (third (substituteVar u v)) alts)
substituteVar u v e@(ELam x body) | v == x = e
                                  | otherwise = ELam x (substituteVar u v body)
substituteVar u v e = e

allVars :: Ord a => CoreExpr a -> Set a
allVars (EVar x) = singleton x
allVars (EAp e1 e2) = allVars e1 `union` allVars e2
allVars (ELet m b e) = allVarsBinders b `union` allVars e
allVars (ECase e a) = allVars e `union` allVarsAlters a
allVars (ELam x e) = singleton x `union` allVars e
allVars _ = empty

allVarsBinders :: Ord a => NE.NonEmpty (a, CoreExpr a) -> Set a
allVarsBinders b = fromList (map fst bs) `union`
  foldr (union . allVars . snd) empty bs
  where
    bs = NE.toList b

allVarsAlters :: Ord a => NE.NonEmpty (CtorName, [a], CoreExpr a) -> Set a
allVarsAlters a = fromList (concatMap (\(_,x,_) -> x) as) `union`
  foldr (union . (\(_,_,x) -> allVars x)) empty as
  where
    as = NE.toList a

freeVars :: Ord a => CoreExpr a -> Set a
freeVars (EVar x) = fromList [x]
freeVars (EAp e1 e2) = freeVars e1 `union` freeVars e2
freeVars (ELet m b e) =
  freeVarsB `union` (freeVars e `difference` binderVars)
  where
    binderVars = fromList . NE.toList $ NE.map fst b
    freeVarsB = case m of
      Recursive -> freeVarsBinders b `difference` binderVars
      NonRecursive -> freeVarsBinders b
freeVars (ECase e a) = freeVars e `union` freeVarsAlters
  where
    freeVarsAlters = foldr union empty (NE.map freeVarsAlter a)
freeVars (ELam x e) = freeVars e `difference` singleton x
freeVars (ENum e) = empty
freeVars (ECtor e) = empty
freeVars (EPrimitive _) = empty
freeVars EError = empty

freeVarsAlter :: (CtorName, [a], CoreExpr a) -> Set a
freeVarsAlter = undefined

freeVarsBinders :: Ord a => NE.NonEmpty (a, CoreExpr a) -> Set a
freeVarsBinders xs = foldr union empty $
  NE.map (snd . second freeVars) xs
