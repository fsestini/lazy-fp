{-# LANGUAGE PatternSynonyms, LambdaCase, GeneralizedNewtypeDeriving,
             TypeOperators, ScopedTypeVariables #-}

module Core.CaseStripping(
  pattern CSVar, pattern CSCtor, pattern CSLit, pattern CSApp,
  pattern CSLet, pattern CSLam, pattern CSPrim, pattern CSErr,
  pattern CSSel, pattern CSGCase,
  pattern CSVarF, pattern CSCtorF, pattern CSLitF, pattern CSAppF,
  pattern CSLetF, pattern CSLamF, pattern CSPrimF, pattern CSErrF,
  pattern CSSelF, pattern CSGCaseF,
  CSExprBase, CSExpr
) where

import qualified Data.List.NonEmpty as NE
import Data.Bifunctor
import Data.Bifoldable
import Core.Syntax
import AST
import GMachine.Syntax (GSelB(..), GCaseB(..), CtorArity)
import RecursionSchemes

-- Case-stripped expression
newtype CSExprBase a b = CSEB ((
    VarB :++: CtorB :++: LitB :++: AppB :++: LetB
    :++: LamB :++: PrimB :++: ErrB :++: GSelB :++: GCaseB
  ) a b) deriving (Eq)

type CSExpr = FixB CSExprBase

csLet m b e = FixB . CSEB . inj $ LetB m b e
csCase n    = FixB . CSEB . inj $ GCaseB n
csApp e1 e2 = FixB . CSEB . inj $ AppB e1 e2

stripCase :: (() -> Int) -> (() -> CtorArity) -> CoreExpr a -> CSExpr a
stripCase dummy1 dummy2 = cata $ \case
  (ECaseF e a) -> foldl csApp (csCase (dummy1 ()))
                              (NE.map (stripAlter dummy2 e) a)
  (EVarFB e)  -> FixB . CSEB . inj $ e
  (ECtorFB e) -> FixB . CSEB . inj $ e
  (ELitFB e)  -> FixB . CSEB . inj $ e
  (EAppFB e)  -> FixB . CSEB . inj $ e
  (ELetFB e)  -> FixB . CSEB . inj $ e
  (ELamFB e)  -> FixB . CSEB . inj $ e
  (EPrimFB e) -> FixB . CSEB . inj $ e
  (EErrFB e)  -> FixB . CSEB . inj $ e

stripAlter :: (() -> CtorArity) -> CSExpr a -> AlterB a (CSExpr a) -> CSExpr a
stripAlter _     _         (AlterB _    []     e) = e
stripAlter dummy scrutinee (AlterB name (x:xs) e) = csLet NonRecursive binders e
  where
    binders =
      fmap (\(v,i) -> BinderB v (FixB . CSEB. inj $ GSelB (dummy ()) i))
        (NE.zip (x NE.:| xs) (1 NE.:| [2..]))

--------------------------------------------------------------------------------
-- Pattern definitions

pattern CSVar e = (FixB (CSEB (Lb (VarB e))))
pattern CSCtor e = (FixB (CSEB (Rb (Lb (CtorB e)))))
pattern CSLit e = (FixB (CSEB (Rb (Rb (Lb (LitB e))))))
pattern CSApp e1 e2 = (FixB (CSEB (Rb (Rb (Rb (Lb (AppB e1 e2)))))))
pattern CSLet e1 e2 e3 = (FixB (CSEB (Rb (Rb (Rb (Rb (Lb (LetB e1 e2 e3))))))))
pattern CSLam e1 e2 = (FixB (CSEB (Rb (Rb (Rb (Rb (Rb (Lb (LamB e1 e2)))))))))
pattern CSPrim e = (FixB (CSEB (Rb (Rb (Rb (Rb (Rb (Rb (Lb (PrimB e))))))))))
pattern CSErr = (FixB (CSEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Lb ErrB))))))))))
pattern CSSel e1 e2 =
  (FixB (CSEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Lb (GSelB e1 e2))))))))))))
pattern CSGCase e =
  (FixB (CSEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Rb (GCaseB e))))))))))))

pattern CSVarF e = (CSEB (Lb (VarB e)))
pattern CSCtorF e = (CSEB (Rb (Lb (CtorB e))))
pattern CSLitF e = (CSEB (Rb (Rb (Lb (LitB e)))))
pattern CSAppF e1 e2 = (CSEB (Rb (Rb (Rb (Lb (AppB e1 e2))))))
pattern CSLetF e1 e2 e3 = (CSEB (Rb (Rb (Rb (Rb (Lb (LetB e1 e2 e3)))))))
pattern CSLamF e1 e2 = (CSEB (Rb (Rb (Rb (Rb (Rb (Lb (LamB e1 e2))))))))
pattern CSPrimF e = (CSEB (Rb (Rb (Rb (Rb (Rb (Rb (Lb (PrimB e)))))))))
pattern CSErrF = (CSEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Lb ErrB)))))))))
pattern CSSelF e1 e2 =
  (CSEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Lb (GSelB e1 e2)))))))))))
pattern CSGCaseF e =
  (CSEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Rb (GCaseB e)))))))))))
