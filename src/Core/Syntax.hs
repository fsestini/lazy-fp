{-# LANGUAGE UndecidableInstances, FlexibleContexts,
             MultiParamTypeClasses, ScopedTypeVariables, LambdaCase,
             TypeSynonymInstances, TypeFamilies, FlexibleInstances,
             TypeOperators, PatternSynonyms #-}

module Core.Syntax where

import Control.Monad.Reader
import Data.Bifoldable
import Data.Bitraversable
import Data.Bifunctor
import Data.Set hiding (foldr, map)
import qualified Data.List.NonEmpty as NE (map, toList)
import AST
import Data.Comp.Bifun

--------------------------------------------------------------------------------
-- Types of Core expressions

type CoreExpr = Term CoreExprB
type CoreAlter a = AlterB a (CoreExpr a)
type CoreBinder a = BinderB a (CoreExpr a)
type CoreScDefn a = (a, CoreExpr a)

type CoreExprB = VarB :+: CtorB :+: LitB :+: AppB :+: LetB
                 :+: CaseB :+: LamB :+: PrimB :+: ErrB

--------------------------------------------------------------------------------
-- Utility functions

allVars :: Ord a => CoreExpr a -> Set a
allVars = foldr union empty . fmap singleton

substituteVar :: Eq a => a -> a -> CoreExpr a -> CoreExpr a
substituteVar u v = cata $ \case
  (EVarF x) -> if v == x then EVar u else EVar x
  e@(ELamF x body) -> if v == x then Term e else ELam x body
  e -> Term e

coreFreeVars :: Ord a => CoreExpr a -> Set a
coreFreeVars = freeVars

--------------------------------------------------------------------------------
-- Pattern declarations

pattern EVarF e = (Inl (VarB e))
pattern ECtorF e = (Inr (Inl (CtorB e)))
pattern ELitF e = (Inr (Inr (Inl (LitB e))))
pattern EAppF e1 e2 = (Inr (Inr (Inr (Inl (AppB e1 e2)))))
pattern ELetF e1 e2 e3 = (Inr (Inr (Inr (Inr (Inl (LetB e1 e2 e3))))))
pattern ECaseF e1 e2 = (Inr (Inr (Inr (Inr (Inr (Inl (CaseB e1 e2)))))))
pattern ELamF e1 e2 = (Inr (Inr (Inr (Inr (Inr (Inr (Inl (LamB e1 e2))))))))
pattern EPrimF e = (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl (PrimB e)))))))))
pattern EErrF = (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr ErrB))))))))

-- pattern EVarFB e = (CEB (Lb e))
-- pattern ECtorFB e = (CEB (Rb (Lb e)))
-- pattern ELitFB e = (CEB (Rb (Rb (Lb e))))
-- pattern EAppFB e = (CEB (Rb (Rb (Rb (Lb e)))))
-- pattern ELetFB e = (CEB (Rb (Rb (Rb (Rb (Lb e))))))
-- pattern ECaseFB e = (CEB (Rb (Rb (Rb (Rb (Rb (Lb e)))))))
-- pattern ELamFB e = (CEB (Rb (Rb (Rb (Rb (Rb (Rb (Lb e))))))))
-- pattern EPrimFB e = (CEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Lb e)))))))))
-- pattern EErrFB e = (CEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Rb e)))))))))

pattern EVar e = (Term (Inl (VarB e)))
pattern ECtor e = (Term (Inr (Inl (CtorB e))))
pattern ELit e = (Term (Inr (Inr (Inl (LitB e)))))
pattern EApp e1 e2 = (Term (Inr (Inr (Inr (Inl (AppB e1 e2))))))
pattern ELet e1 e2 e3 = (Term (Inr (Inr (Inr (Inr (Inl (LetB e1 e2 e3)))))))
pattern ECase e1 e2 = (Term (Inr (Inr (Inr (Inr (Inr (Inl (CaseB e1 e2))))))))
pattern ELam e1 e2 =
  (Term (Inr (Inr (Inr (Inr (Inr (Inr (Inl (LamB e1 e2)))))))))
pattern EPrim e =
  (Term (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inl (PrimB e))))))))))
pattern EErr = (Term (Inr (Inr (Inr (Inr (Inr (Inr (Inr (Inr ErrB)))))))))
