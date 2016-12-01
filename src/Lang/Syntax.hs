module Lang.Syntax where

import Data.List.NonEmpty

type Program a = [Either DataDecl (LangExpr a)]
type DataDecl = (Name, [CtorDecl])
type CtorDecl = (Name, [Name])
type Name = String
type CtorName = Name
type Binder a = (Name, LangExpr a)
type Alter a = (CtorName, [a], LangExpr a)
type ScDefn a = (a, [Pattern a], LangExpr a)

data LangExpr a = Var a
            | Ctor CtorName
            | Lam [a] (LangExpr a)
            | Let LetMode (NonEmpty (Binder a)) (LangExpr a)
            | Case (LangExpr a) (NonEmpty (Alter a))
            | App (LangExpr a) (LangExpr a)
            | Lit Lit
            | PrimOp PrimOp
            deriving (Eq,Show)

data Pattern a = PVar a
               | PInt Int
               | PCtor CtorName [Pattern a]
               deriving (Eq,Show)

data LetMode = Recursive | NonRecursive deriving (Eq, Show)
data Lit = LInt Int deriving (Show, Eq, Ord)
data PrimOp = Add | Sub | Mul | Eql deriving (Eq, Ord, Show)
