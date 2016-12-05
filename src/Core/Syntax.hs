module Core.Syntax where

import Data.Set hiding (foldr, map)
import Lang.Syntax(LangExpr(..), Lit(..), PrimOp, LetMode(..), Name, CtorName)
import Control.Arrow (second)
import Data.List.NonEmpty(NonEmpty(..), map, toList)
import Utils

type CoreAlter a = (CtorName, [a], CoreExpr a)
type CoreScDefn a = (a, [a], CoreExpr a)

data CoreExpr a = EVar a
            | ENum Int
            | ECtor CtorName
            | EAp (CoreExpr a) (CoreExpr a)
            | ELet LetMode (NonEmpty (a, CoreExpr a)) (CoreExpr a)
            | ECase (CoreExpr a) (NonEmpty (CoreAlter a))
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
  ELet mode (Data.List.NonEmpty.map (second (substituteVar u v)) binds) (substituteVar u v e)
substituteVar u v (ECase e alts) =
  ECase (substituteVar u v e) (Data.List.NonEmpty.map (third (substituteVar u v)) alts)
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

allVarsBinders :: Ord a => NonEmpty (a, CoreExpr a) -> Set a
allVarsBinders b = fromList (Prelude.map fst bs) `union`
  foldr (union . allVars . snd) empty bs
  where
    bs = Data.List.NonEmpty.toList b

allVarsAlters :: Ord a => NonEmpty (CtorName, [a], CoreExpr a) -> Set a
allVarsAlters a = fromList (concatMap (\(_,x,_) -> x) as) `union`
  foldr (union . (\(_,_,x) -> allVars x)) empty as
  where
    as = Data.List.NonEmpty.toList a

freeVars :: Ord a => CoreExpr a -> Set a
freeVars = undefined
-- freeVars (EVar x) = fromList [x]
-- freeVars (ENum e) = empty
-- freeVars (ECtor e) = empty
-- freeVars (EAp e1 e2) = freeVars e1 `union` freeVars e2
-- freeVars (ELet Recursive b e) =
--   (freeVarsBinders b `difference` binderVars)
--   `union` (freeVars e `difference` binderVars)
--   where
--     binderVars = fromList $ Prelude.map fst $ Data.List.NonEmpty.toList b
-- freeVars (ELet NonRecursive b e) =
--   freeVarsBinders b `union` (freeVars e `difference` binderVars)
--   where
--     binderVars = fromList $ Prelude.map fst $ Data.List.NonEmpty.toList b
-- freeVars (ECase e a) = undefined
-- freeVars (ELam e1 e2) = undefined
-- freeVars (EPrimitive e) = undefined
-- freeVars EError = undefined
--
-- freeVarsBinders :: Ord a => NonEmpty (a, CoreExpr a) -> Set a
-- freeVarsBinders xs = foldr union empty $
--   Data.List.NonEmpty.map (snd . second freeVars) xs
