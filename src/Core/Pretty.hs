{-# LANGUAGE LambdaCase, TypeSynonymInstances, FlexibleInstances #-}

module Core.Pretty where

import AST
import qualified Data.List.NonEmpty as NE
import Text.PrettyPrint.HughesPJ
import Text.PrettyPrint hiding(Pretty)
import Core.Syntax
import RecursionSchemes

-- <super-hack>

class Pretty a where
  pPrint :: a -> Doc

instance Pretty String where
  pPrint = text

-- </super-hack>

pExpr :: Pretty a => CoreExpr a -> Doc
pExpr = cata $ \case
  (EVarF x)        -> pPrint x
  (ELitF (LInt n)) -> integer (toInteger n)
  (ECtorF name)    -> pPrint name
  (EAppF d1 d2)    -> hsep [parens d1, parens d2]
  (ELetF m b e)    -> pLetLetrec m b e
  (ECaseF e a)     -> pCase e a
  (ELamF x e)      -> hsep [text "\\", pPrint x, text "->", e]
  (EPrimF Add)     -> text "add#"
  (EPrimF Sub)     -> text "sub#"
  (EPrimF Mul)     -> text "mul#"
  (EPrimF Eql)     -> text "eql#"
  EErrF            -> text "error"

pLetLetrec :: Pretty a => LetMode -> NE.NonEmpty (BinderB a Doc) -> Doc -> Doc
pLetLetrec m b e = vcat $ keyword : binders ++ [text "in", nest 2 e]
  where
    keyword = recNonRec m (text "letrec") (text "let")
    binders = NE.toList $ NE.map (nest 2 . pBinder) b
    pBinder (BinderB x e) = hsep [pPrint x, equals, e]

pCase :: Pretty a => Doc -> NE.NonEmpty (AlterB a Doc) -> Doc
pCase e alters =
  vcat $ hsep [text "case", e, text "of"]
       : map (nest 2 . pAlter) (NE.toList alters)
  where
    pAlter (AlterB name vars e) =
      hsep $ pPrint name : map pPrint vars ++ [text "->", e]
