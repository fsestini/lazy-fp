module Core.Syntax where

import Lang.Syntax(PrimOp, LetMode, Name, CtorName)
import Control.Arrow (second)

third :: (c -> d) -> (a,b,c) -> (a,b,d)
third f (x,y,z) = (x,y,f z)

type CoreAlter a = (a, [a], CoreExpr a)
type CoreScDefn a = (a, [a], CoreExpr a)

data CoreExpr a = EVar a
            | ENum Int
            | ECtor CtorName
            | EAp (CoreExpr a) (CoreExpr a)
            | ELet LetMode [(a, CoreExpr a)] (CoreExpr a)
            | ECase (CoreExpr a) [CoreAlter a]
            | ELam a (CoreExpr a)
            | EPrimitive PrimOp -- primitive operations
            deriving (Eq, Show)

-- [u/v]e, where u is fresh
substituteVar :: Eq a => a -> a -> CoreExpr a -> CoreExpr a
substituteVar u v (EVar x) | v == x = EVar u
                           | otherwise = EVar x
substituteVar u v (EAp e1 e2) =
  EAp (substituteVar u v e1) (substituteVar u v e2)
substituteVar u v (ELet mode binds e) =
  ELet mode (map (second (substituteVar u v)) binds) (substituteVar u v e)
substituteVar u v (ECase e alts) =
  ECase (substituteVar u v e) (map (third (substituteVar u v)) alts)
substituteVar u v e@(ELam x body) | v == x = e
                                  | otherwise = ELam x (substituteVar u v body)
substituteVar u v e = e

freeVars :: CoreExpr a -> [a]
freeVars = error "not implemented: Core.Syntax.freeVars"
