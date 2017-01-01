{-# LANGUAGE PatternSynonyms, LambdaCase, ScopedTypeVariables,
             FlexibleContexts, TypeOperators #-}

module Core.CaseStripping(CSExpr, CSExprBase, CSScDefn) where

import qualified Data.List.NonEmpty as NE
import Data.Bifunctor
import Data.Bifoldable
import Core.Syntax
import AST
import Data.Proxy
import GMachine.Syntax (GSelB(..), GCaseB(..), CtorArity, iGCase)
import Data.Comp.Bifun

type CommonBase = VarB :+: CtorB :+: LitB :+: AppB
                  :+: LetB :+: LamB :+: PrimB :+: ErrB
type CSExprBase = CommonBase :+: GSelB :+: GCaseB

-- Case-stripped expression
type CSExpr = Term CSExprBase
type CSScDefn v = (v, CSExpr v)

stripCase :: (() -> Int) -> (() -> CtorArity) -> CoreExpr a -> CSExpr a
stripCase dummy1 dummy2 = splitAlg f g
  where
    f (CaseB e a) = foldl iApp (iGCase (dummy1 ()))
                          (fmap (stripAlter dummy2 e) a)
    g :: CommonBase v (CSExpr v) -> CSExpr v
    g = inject

stripAlter :: forall a . (() -> CtorArity) -> CSExpr a -> AlterB a (CSExpr a) -> CSExpr a
stripAlter _     _         (AlterB _    []     e) = e
stripAlter dummy scrutinee (AlterB name (x:xs) e) = iLet NonRecursive binders e
  where
    binders = fmap (\(v,i) ->
      BinderB v (inject (GSelB (dummy ()) i)))
        (NE.zip (x NE.:| xs) (NE.fromList [1..]))
