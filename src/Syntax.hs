module Syntax where

type Name = String
type CtorTag = Int
type CtorArity = Int

data LetMode = Recursive | NonRecursive deriving (Eq, Show)
data BinOp = Plus | Minus | Mult | Div deriving (Eq, Show)
data Expr a = EVar Name
            | ENum Int
            | EBinOp BinOp (Expr a) (Expr a)
            | ECtor CtorTag CtorArity
            | EAp (Expr a) (Expr a)
            | ELet LetMode [(a, Expr a)] (Expr a)
            | ECase (Expr a) [Alter a]
            | ELam [a] (Expr a)
            deriving (Eq, Show)

type CoreExpr = Expr Name

bindersOf :: [(a,b)] -> [a]
bindersOf = map fst

rhssOf :: [(a,b)] -> [b]
rhssOf = map snd

-- case expressions have an expression to analyze, and a list of alternatives.
-- Each alternative contains a tag, a list of the bound variables and the
-- expression to the right of the arrow.

type Alter a = (CtorTag, [a], Expr a)
type CoreAlt = Alter Name

isAtomicExpr :: Expr a -> Bool
isAtomicExpr (EVar v) = True
isAtomicExpr (ENum n) = True
isAtomicExpr _ = False

-- Supercombinator definition
type ScDefn a = (Name, [a], Expr a)
type CoreScDefn = ScDefn Name

type Program a = [ScDefn a]
type CoreProgram = Program Name

----------------------------------------
-- Standard prelude

preludeDefs :: CoreProgram
preludeDefs = [
  ("I", ["x"], EVar "x"),
  ("K", ["x", "y"], EVar "x"),
  ("K1", ["x", "y"], EVar "y"),
  ("S", ["f", "g", "x"], EAp (EAp (EVar "f") (EVar "x")) (EAp (EVar "g") (EVar "x"))),
  ("compose", ["f", "g", "x"], EAp (EVar "f") (EAp (EVar "g") (EVar "x"))),
  ("twice", ["f"], EAp (EAp (EVar "compose") (EVar "f")) (EVar "f"))
   ]
