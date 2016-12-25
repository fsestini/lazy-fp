{-# LANGUAGE PatternSynonyms, GeneralizedNewtypeDeriving, TypeOperators,
             TemplateHaskell #-}

module GMachine.Syntax (
  Name, CtorTag, CtorArity, LetMode(..), PrimOp(..), Lit(..),
  GExpr(..), bindersOf, rhssOf,
  GAlterB(..), GAlter, GBinders,
  isAtomicExpr,
  pattern GVarF, pattern GLitF, pattern GPackF, pattern GAppF,
  pattern GLetF, pattern GPrimF, pattern GVar, pattern GLit, pattern GPack,
  pattern GApp, pattern GLet, pattern GPrim,
  GScDefn, GProgram, GProgramN, GExprN, GScDefnN, GAlterN, GBindersN,
  preludeDefs,
  GSelB(..), GCaseB(..)
) where

import qualified Data.List.NonEmpty as NE
import AssocList
import AST
import RecursionSchemes
import Data.Bifunctor
import Data.Bifunctor.TH
import Data.Bifoldable
import Data.Bitraversable

type CtorTag = Int

data GPackB a b = GPackB CtorTag CtorArity
  deriving (Eq, Show, Ord)
$(deriveBifunctor ''GPackB)
$(deriveBifoldable ''GPackB)
$(deriveBitraversable ''GPackB)

data GCaseB a b = GCaseB Int
  deriving(Eq, Ord, Show)
$(deriveBifunctor ''GCaseB)
$(deriveBifoldable ''GCaseB)
$(deriveBitraversable ''GCaseB)

data GSelB a b = GSelB CtorArity Int
  deriving (Eq, Ord, Show)
$(deriveBifunctor ''GSelB)
$(deriveBifoldable ''GSelB)
$(deriveBitraversable ''GSelB)

newtype GExprBase a b = GEB ((
    VarB :++: LitB :++: GPackB :++: AppB :++: LetB :++: PrimB
    :++: GSelB :++: GCaseB
  ) a b) deriving (Bifunctor, Bifoldable)

instance Bitraversable GExprBase where
  bitraverse f g (GEB x) = GEB <$> bitraverse f g x

type GExpr = FixB GExprBase

-- data GExpr a = GVar Name
--              | GLit Lit
--              | GPack CtorTag CtorArity
--              | GApp (GExpr a) (GExpr a)
--              | GLet LetMode (NE.NonEmpty (BinderB a (GExpr a))) (GExpr a)
--              | GCase (GExpr a) [GAlterB a (GExpr a)]
--              | GPrim PrimOp
--              deriving (Eq, Show)

bindersOf :: NE.NonEmpty (a,b) -> NE.NonEmpty a
bindersOf = NE.map fst

rhssOf :: NE.NonEmpty (a,b) -> NE.NonEmpty b
rhssOf = NE.map snd

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

pattern GVarF x        = (GEB (Lb (VarB x)))
pattern GLitF x        = (GEB (Rb (Lb (LitB x))))
pattern GPackF x1 x2   = (GEB (Rb (Rb (Lb (GPackB x1 x2)))))
pattern GAppF x1 x2    = (GEB (Rb (Rb (Rb (Lb (AppB x1 x2))))))
pattern GLetF x1 x2 x3 = (GEB (Rb (Rb (Rb (Rb (Lb (LetB x1 x2 x3)))))))
pattern GPrimF x       = (GEB (Rb (Rb (Rb (Rb (Rb (Lb (PrimB x))))))))
pattern GSelF a i      = (GEB (Rb (Rb (Rb (Rb (Rb (Rb (Lb (GSelB a i)))))))))
pattern GCaseF t       = (GEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (GCaseB t)))))))))

pattern GVar x        = FixB (GEB (Lb (VarB x)))
pattern GLit x        = FixB (GEB (Rb (Lb (LitB x))))
pattern GPack x1 x2   = FixB (GEB (Rb (Rb (Lb (GPackB x1 x2)))))
pattern GApp x1 x2    = FixB (GEB (Rb (Rb (Rb (Lb (AppB x1 x2))))))
pattern GLet x1 x2 x3 = FixB (GEB (Rb (Rb (Rb (Rb (Lb (LetB x1 x2 x3)))))))
pattern GPrim x       = FixB (GEB (Rb (Rb (Rb (Rb (Rb (Lb (PrimB x))))))))
pattern GSel a i
  = FixB (GEB (Rb (Rb (Rb (Rb (Rb (Rb (Lb (GSelB a i)))))))))
pattern GCase t       = FixB (GEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (GCaseB t)))))))))
