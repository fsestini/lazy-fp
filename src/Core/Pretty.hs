module Core.Pretty where

import Lang.Syntax(LetMode(..), PrimOp(..))
import Text.PrettyPrint.HughesPJClass
import Text.PrettyPrint
import Core.Syntax

pExpr :: Pretty a => CoreExpr a -> Doc
pExpr (EVar x) = pPrint x
pExpr (ENum n) = integer (toInteger n)
pExpr (ECtor name) = pPrint name
pExpr (EAp e1 e2) = hsep [parens (pExpr e1), parens (pExpr e2)]
pExpr (ELet mode b e) = pLetLetrec mode b e
pExpr (ECase e a) = pCase e a
pExpr (ELam x e) = pLambda x e
pExpr (EPrimitive Add) = text "#add"
pExpr (EPrimitive Sub) = text "#sub"
pExpr (EPrimitive Mul) = text "#mul"
pExpr (EPrimitive Eql) = text "#eql"

pBinder :: Pretty a => (a,CoreExpr a) -> Doc
pBinder (x,e) = hsep [pPrint x, equals, pExpr e]

pLambda :: Pretty a => a -> CoreExpr a -> Doc
pLambda x e = hsep [text "\\", pPrint x, text "->", pExpr e]

pLetLetrec :: Pretty a => LetMode -> [(a,CoreExpr a)] -> CoreExpr a -> Doc
pLetLetrec m b e = vcat $ keyword : binders ++ [text "in", pExpr e]
  where
    keyword = case m of
      Recursive -> text "letrec"
      NonRecursive -> text "let"
    binders = map (nest 2 . pBinder) b

pAlter :: Pretty a => CoreAlter a -> Doc
pAlter (ctorName,vars,e) =
  hsep $ pPrint ctorName : map pPrint vars ++ [text "->", pExpr e]

pCase :: Pretty a => CoreExpr a -> [CoreAlter a] -> Doc
pCase e alters =
  vcat $ hsep [text "case", pExpr e] : map (nest 2 . pAlter) alters
