module Core.Pretty where

import AST
import Text.PrettyPrint
import Core.Syntax
import PrettyClass
import Data.Comp.Bifun

pExpr :: Pretty a => CoreExpr a -> Doc
pExpr = cata prettyAlg
