module Core.Syntax where

import Lang.Syntax(PrimOp, LetMode, Name, CtorName)
import Control.Arrow (second)

third :: (c -> d) -> (a,b,c) -> (a,b,d)
third f (x,y,z) = (x,y,f z)

type Alter a = (a, [a], Expr a)
type ScDefn a = (a, [a], Expr a)

data Expr a = EVar a
            | ENum Int
            | ECtor CtorName
            | EAp (Expr a) (Expr a)
            | ELet LetMode [(a, Expr a)] (Expr a)
            | ECase (Expr a) [Alter a]
            | ELam a (Expr a)
            | EPrimitive PrimOp -- primitive operations
            deriving (Eq, Show)

type CoreAlter = Alter Name
type CoreExpr = Expr Name
type CoreScDefn = ScDefn Name

-- [u/v]e, where u is fresh
substituteVar :: Eq a => a -> a -> Expr a -> Expr a
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
