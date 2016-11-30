module Lang.Syntax where

import Data.List.NonEmpty

type Program a = [Either DataDecl (Expr a)]
type DataDecl = (Name, [CtorDecl])
type CtorDecl = (Name, [Name])
type Name = String
type Binder a = (Name, Expr a)
type Alter a = (a, [a], Expr a)
type ScDefn a = (a, [Pattern a], Expr a)

data Expr a = Var a
            | Lam [a] (Expr a)
            | Let LetMode (NonEmpty (Binder a)) (Expr a)
            | Case a (NonEmpty (Alter a))
            | App (Expr a) (Expr a)
            | Lit Lit
            | PrimOp PrimOp
            deriving (Eq,Show)

data Pattern a = PVar a
               | PInt Int
               | PCtor a [Pattern a]
               deriving (Eq,Show)

data LetMode = Recursive | NonRecursive deriving (Eq, Show)
data Lit = LInt Int deriving (Show, Eq, Ord)
data PrimOp = Add | Sub | Mul | Eql deriving (Eq, Ord, Show)
