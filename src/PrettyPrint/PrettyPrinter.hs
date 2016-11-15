module PrettyPrint.PrettyPrinter where

import Syntax
import PrettyPrint.ISeq

-----------------------
-- Pretty-printer

pprint :: CoreProgram -> String
pprint = iDisplay . pprProgram

pprProgram :: CoreProgram -> ISeq
pprProgram = iInterleave iNewLine . map pprCoreScDefn

pprCoreScDefn :: CoreScDefn -> ISeq
pprCoreScDefn (name, vars, expr) = iConcat [
    iStr name, iStr " ",
    iInterleave (iStr " ") (map iStr vars),
    iStr " = ", pprExpr expr ]

pprExpr :: CoreExpr -> ISeq
pprExpr (ENum n) = iStr $ show n
pprExpr (EVar v) = iStr v
pprExpr (EAp e1 e2) = pprExpr e1 `iAppend` iStr " " `iAppend` pprAExpr e2
pprExpr (ELet mode defns expr) = iConcat [
    iStr (keyword mode), iNewLine,
    iStr "  ", iIndent (pprDefns defns), iNewLine,
    iStr "in ", pprExpr expr ]
  where
    keyword Recursive = "letrec"
    keyword NonRecursive = "let"
pprExpr (ECase expr alterns) = iConcat [
    iStr "case ", pprExpr expr, iStr " of", iNewLine,
    iStr "  ", iIndent (pprAlterns alterns) ]

pprAlterns :: [CoreAlt] -> ISeq
pprAlterns alts = iInterleave iNewLine (map pprAlt alts)

pprAlt :: CoreAlt -> ISeq
pprAlt (tag, boundVars, expr) = iConcat [
    iStr ("<" ++ show tag ++ "> "),
    iInterleave (iStr " ") (map iStr boundVars),
    iStr " -> ", pprExpr expr ]

pprAExpr :: CoreExpr -> ISeq
pprAExpr e | isAtomicExpr e = pprExpr e
pprAExpr e = iStr "(" `iAppend` pprExpr e `iAppend` iStr ")"

pprDefns :: [(Name, CoreExpr)] -> ISeq
pprDefns defns = iInterleave separator (map pprDefn defns)
  where
    separator = iConcat [ iStr ";", iNewLine ]

pprDefn :: (Name, CoreExpr) -> ISeq
pprDefn (name, expr) = iConcat [ iStr name, iStr " = ", iIndent (pprExpr expr) ]
