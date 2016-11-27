module Lang.Syntax where

type Name = String
type TypeName = Name
type CtorName = Name
type AdtCtor = (CtorName, [TypeName])
type AdtDecl = (TypeName, [AdtCtor])

type Alter a = (CtorName, [a], Expr a)
type LangAlter = Alter Name

data LetMode = Recursive | NonRecursive deriving (Eq, Show)
data BinOp = Plus | Minus | Mult | Div deriving (Eq, Show)

data PrimOp = PrimComp | PrimSum | PrimSub | PrimMul | PrimDiv
            deriving (Eq,Show)

data Expr a = EVar a
            | ENum Int
            | ECtor CtorName
            | EAp (Expr a) (Expr a)
            | ELet LetMode [(a, Expr a)] (Expr a)
            | ECase (Expr a) [Alter a]
            | ELam a (Expr a)
            | EPrimitive PrimOp -- primitive operations
            deriving (Eq, Show)

type LangExpr = Expr Name

type ScDefn a = (a, [a], Expr a)
type LangScDefn = ScDefn Name

type Program a = ([AdtDecl],[ScDefn a])
type LangProgram = Program Name
