{-# LANGUAGE PatternSynonyms, GeneralizedNewtypeDeriving, TypeOperators,
             TemplateHaskell, LiberalTypeSynonyms, DeriveFunctor,
             DeriveFoldable, DeriveTraversable, FlexibleContexts,
             FlexibleInstances, MultiParamTypeClasses #-}

module GMachine.Syntax (
  Name, CtorTag, CtorArity, LetMode(..), PrimOp(..), Lit(..),
  GExpr(..), GAlterB(..), GAlter, GBinders,
  isAtomicExpr,
  pattern GVarF, pattern GLitF, pattern GPackF, pattern GAppF,
  pattern GLetF, pattern GPrimF, pattern GVar, pattern GLit, pattern GPack,
  pattern GApp, pattern GLet, pattern GPrim,
  GScDefn, GProgram, GProgramN, GExprN, GScDefnN, GAlterN, GBindersN,
  preludeDefs,
  GSelB(..), GCaseB(..), iGCase
) where

import qualified Data.List.NonEmpty as NE
import qualified Data.Set as S
import AssocList
import AST
import Data.Bifunctor
import Data.Bifunctor.TH
import Data.Bifoldable
import Data.Bitraversable
import Data.Comp.Bifun

type CtorTag = Int

data GPackB a b = GPackB CtorTag CtorArity
  deriving (Eq, Show, Ord)

iGCase :: (GCaseB :<: f) => Int -> Term f a
iGCase = inject . GCaseB

data GCaseB a b = GCaseB Int
  deriving (Eq, Show, Ord)

data GSelB a b = GSelB CtorArity Int
  deriving (Eq, Show, Ord)

$(deriveBifunctor ''GSelB)
$(deriveBifunctor ''GCaseB)
$(deriveBifoldable ''GSelB)
$(deriveBifoldable ''GCaseB)
$(deriveBitraversable ''GSelB)
$(deriveBitraversable ''GCaseB)

type GExprBaseB = VarB :+: LitB :+: GPackB :+: AppB
                  :+: LetB :+: PrimB :+: GSelB :+: GCaseB

type GExpr = Term GExprBaseB

-- case expressions have an expression to analyze, and a list of alternatives.
-- Each alternative contains a tag, a list of the bound variables and the
-- expression to the right of the arrow.

data GAlterB a b = GAlterB CtorTag [a] b
  deriving (Eq, Ord, Show)

isAtomicExpr :: GExpr a -> Bool
isAtomicExpr (GVar v) = True
isAtomicExpr (GLit _) = True
isAtomicExpr _ = False

type GAlter a = GAlterB a (GExpr a)
type GBinders a = Assoc a (GExpr a)
type GScDefn a = (Name, [a], GExpr a)
type GProgram a = [GScDefn a]
type GProgramN = GProgram Name
type GExprN = GExpr Name
type GScDefnN = GScDefn Name
type GAlterN = GAlterB Name GExprN
type GBindersN = NE.NonEmpty (BinderB Name GExprN)

----------------------------------------
-- Standard prelude

preludeDefs :: GProgram Name
preludeDefs = [
  ("I", ["x"], GVar "x"),
  ("K", ["x", "y"], GVar "x"),
  ("K1", ["x", "y"], GVar "y"),
  ("S", ["f", "g", "x"], GApp (GApp (GVar "f") (GVar "x")) (GApp (GVar "g") (GVar "x"))),
  ("compose", ["f", "g", "x"], GApp (GVar "f") (GApp (GVar "g") (GVar "x"))),
  ("twice", ["f"], GApp (GApp (GVar "compose") (GVar "f")) (GVar "f"))
  -- , ("if", ["b", "x", "y"], GCase (GVar "b") [(2,[],GVar "x"),(1,[],GVar "y")])
   ]

--------------------------------------------------------------------------------
-- Pattern definitions

pattern GVarF x        = (Inl (VarB x))
pattern GLitF x        = (Inr (Inl (LitB x)))
pattern GPackF x1 x2   = (Inr (Inr (Inl (GPackB x1 x2))))
pattern GAppF x1 x2    = (Inr (Inr (Inr (Inl (AppB x1 x2)))))
pattern GLetF x1 x2 x3 = (Inr (Inr (Inr (Inr (Inl (LetB x1 x2 x3))))))
pattern GPrimF x       = (Inr (Inr (Inr (Inr (Inr (Inl (PrimB x)))))))
pattern GSelF a i      = (Inr (Inr (Inr (Inr (Inr (Inr (Inl (GSelB a i))))))))
pattern GCaseF t       = (Inr (Inr (Inr (Inr (Inr (Inr (Inr (GCaseB t))))))))

pattern GVar x        = Term (Inl (VarB x))
pattern GLit x        = Term (Inr (Inl (LitB x)))
pattern GPack x1 x2   = Term (Inr (Inr (Inl (GPackB x1 x2))))
pattern GApp x1 x2    = Term (Inr (Inr (Inr (Inl (AppB x1 x2)))))
pattern GLet x1 x2 x3 = Term (Inr (Inr (Inr (Inr (Inl (LetB x1 x2 x3))))))
pattern GPrim x       = Term (Inr (Inr (Inr (Inr (Inr (Inl (PrimB x)))))))
pattern GSel a i      =
  Term (Inr (Inr (Inr (Inr (Inr (Inr (Inl (GSelB a i))))))))
pattern GCase t       =
  Term (Inr (Inr (Inr (Inr (Inr (Inr (Inr (GCaseB t))))))))
