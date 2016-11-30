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
