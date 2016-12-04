module Lang.Syntax where

import Data.List(nub)
import Data.List.NonEmpty(toList, NonEmpty(..))

type Program a = [Either DataDecl (LangExpr a)]
type DataDecl = (CtorName, NonEmpty CtorDecl)
type CtorDecl = (CtorName, NonEmpty CtorName)
type Name = String
type CtorName = Name
type Binder a = (Pattern a, LangExpr a)
type Alter a = (CtorName, [a], LangExpr a)
type ScDefn a = (a, [Pattern a], LangExpr a)

--------------------------------------------------------------------------------
-- Supercombinator definitions

scName :: ScDefn a -> a
scName (x,_,_) = x

getScNames :: Eq a => [ScDefn a] -> [a]
getScNames defns = nub $ map scName defns

chunkByName :: Eq a => [ScDefn a] -> [(a, [([Pattern a], LangExpr a)])]
chunkByName defns = flip map names $ \name ->
  (name, map (\(x,y,z) -> (y,z)) $ filter ((== name) . scName) defns)
  where
    names = getScNames defns

termConstructors :: DataDecl -> [(CtorName, Int)]
termConstructors (typeName,decls) =
  map (\decl -> (fst decl, length . snd $ decl)) (toList decls) -- TODO: fix

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

patternFreeVars :: Pattern a -> [a]
patternFreeVars (PVar x) = [x]
patternFreeVars (PInt _) = []
patternFreeVars (PCtor _ ps) = concatMap patternFreeVars ps
