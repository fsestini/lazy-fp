{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Core.Pretty where

import Data.List.NonEmpty
import Lang.Syntax(LetMode(..), PrimOp(..))
import Text.PrettyPrint.HughesPJ
--import Text.PrettyPrint.HughesPJClass(Pretty, pPrint)
import Text.PrettyPrint hiding(Pretty)
import Core.Syntax

-- <super-hack>

class Pretty a where
  pPrint :: a -> Doc

instance Pretty String where
  pPrint = text

-- </super-hack>

pExpr :: Pretty a => CoreExpr a -> Doc
pExpr (EVar x) = pPrint x
pExpr (ENum n) = integer (toInteger n)
pExpr (ECtor name) = pPrint name
pExpr (EAp e1 e2) = hsep [parens (pExpr e1), parens (pExpr e2)]
pExpr (ELet mode b e) = pLetLetrec mode b e
pExpr (ECase e a) = pCase e a
pExpr (ELam x e) = pLambda x e
pExpr (EPrimitive Add) = text "add#"
pExpr (EPrimitive Sub) = text "sub#"
pExpr (EPrimitive Mul) = text "mul#"
pExpr (EPrimitive Eql) = text "eql#"
pExpr EError = text "error"

pBinder :: Pretty a => (a,CoreExpr a) -> Doc
pBinder (x,e) = hsep [pPrint x, equals, pExpr e]

pLambda :: Pretty a => a -> CoreExpr a -> Doc
pLambda x e = hsep [text "\\", pPrint x, text "->", pExpr e]

pLetLetrec :: Pretty a => LetMode -> NonEmpty (a,CoreExpr a) -> CoreExpr a -> Doc
pLetLetrec m b e = vcat $ keyword : binders ++ [text "in", pExpr e]
  where
    keyword = case m of
      Recursive -> text "letrec"
      NonRecursive -> text "let"
    binders = toList $ Data.List.NonEmpty.map (nest 2 . pBinder) b

pAlter :: Pretty a => CoreAlter a -> Doc
pAlter (ctorName,vars,e) =
  hsep $ pPrint ctorName : Prelude.map pPrint vars ++ [text "->", pExpr e]

pCase :: Pretty a => CoreExpr a -> NonEmpty (CoreAlter a) -> Doc
pCase e alters =
  vcat $ hsep [text "case", pExpr e] : Prelude.map (nest 2 . pAlter) (toList alters)
