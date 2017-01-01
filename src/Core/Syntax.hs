{-# LANGUAGE UndecidableInstances, FlexibleContexts, MultiParamTypeClasses,
            ScopedTypeVariables, LambdaCase, TypeSynonymInstances,
            TypeFamilies, FlexibleInstances, TypeOperators, PatternSynonyms,
            GeneralizedNewtypeDeriving #-}

module Core.Syntax where

import Data.Bifoldable
import Data.Bitraversable
import Data.Bifunctor
import Data.Set hiding (foldr, map)
import qualified Data.List.NonEmpty as NE (map, toList)
import RecursionSchemes
import AST

--------------------------------------------------------------------------------
-- Types of Core expressions

type CoreExpr = FixB CoreExprBase
type CoreAlter a = AlterB a (CoreExpr a)
type CoreBinder a = BinderB a (CoreExpr a)
type CoreScDefn a = (a, CoreExpr a)

type CoreExprBaseB = VarB :++: CtorB :++: LitB :++: AppB :++: LetB :++: CaseB
                     :++: LamB :++: PrimB :++: ErrB
newtype CoreExprBase a b = CEB (CoreExprBaseB a b)
  deriving (Bifunctor, Bifoldable, Eq, Ord, Show)

instance Bitraversable CoreExprBase where
  bitraverse f g (CEB x) = CEB <$> bitraverse f g x

--------------------------------------------------------------------------------
-- Utility functions

allVars :: Ord a => CoreExpr a -> Set a
allVars = foldr union empty . fmap singleton

substituteVar :: Eq a => a -> a -> CoreExpr a -> CoreExpr a
substituteVar u v = cata $ \case
  (EVarF x) -> if v == x then EVar u else EVar x
  e@(ELamF x body) -> if v == x then FixB e else ELam x body
  e -> FixB e

freeVars :: Ord a => CoreExpr a -> Set a
freeVars = cata $ \case
  (EVarF x)     -> singleton x
  (EAppF s1 s2) -> s1 `union` s2
  (ELetF m b s) -> bFreeVars `union` (s `difference` binderVars)
    where
      binderVars = fromList . NE.toList $ NE.map binderVar b
      bodiesFreeVars = foldr union empty $ NE.map binderBody b
      bFreeVars = bodiesFreeVars `difference` recNonRec m binderVars empty
  (ECaseF s a)  -> s `union` foldr (union . afv) empty a
    where afv (AlterB _ vars s') = s' `difference` fromList vars
  (ELamF x s)   -> s `difference` singleton x
  _            -> empty

--------------------------------------------------------------------------------
-- Pattern declarations

pattern EVarF e = (CEB (Lb (VarB e)))
pattern ECtorF e = (CEB (Rb (Lb (CtorB e))))
pattern ELitF e = (CEB (Rb (Rb (Lb (LitB e)))))
pattern EAppF e1 e2 = (CEB (Rb (Rb (Rb (Lb (AppB e1 e2))))))
pattern ELetF e1 e2 e3 = (CEB (Rb (Rb (Rb (Rb (Lb (LetB e1 e2 e3)))))))
pattern ECaseF e1 e2 = (CEB (Rb (Rb (Rb (Rb (Rb (Lb (CaseB e1 e2))))))))
pattern ELamF e1 e2 = (CEB (Rb (Rb (Rb (Rb (Rb (Rb (Lb (LamB e1 e2)))))))))
pattern EPrimF e = (CEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Lb (PrimB e))))))))))
pattern EErrF = (CEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Rb ErrB)))))))))

pattern EVarFB e = (CEB (Lb e))
pattern ECtorFB e = (CEB (Rb (Lb e)))
pattern ELitFB e = (CEB (Rb (Rb (Lb e))))
pattern EAppFB e = (CEB (Rb (Rb (Rb (Lb e)))))
pattern ELetFB e = (CEB (Rb (Rb (Rb (Rb (Lb e))))))
pattern ECaseFB e = (CEB (Rb (Rb (Rb (Rb (Rb (Lb e)))))))
pattern ELamFB e = (CEB (Rb (Rb (Rb (Rb (Rb (Rb (Lb e))))))))
pattern EPrimFB e = (CEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Lb e)))))))))
pattern EErrFB e = (CEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Rb e)))))))))

pattern EVar e = (FixB (CEB (Lb (VarB e))))
pattern ECtor e = (FixB (CEB (Rb (Lb (CtorB e)))))
pattern ELit e = (FixB (CEB (Rb (Rb (Lb (LitB e))))))
pattern EApp e1 e2 = (FixB (CEB (Rb (Rb (Rb (Lb (AppB e1 e2)))))))
pattern ELet e1 e2 e3 = (FixB (CEB (Rb (Rb (Rb (Rb (Lb (LetB e1 e2 e3))))))))
pattern ECase e1 e2 = (FixB (CEB (Rb (Rb (Rb (Rb (Rb (Lb (CaseB e1 e2)))))))))
pattern ELam e1 e2
  = (FixB (CEB (Rb (Rb (Rb (Rb (Rb (Rb (Lb (LamB e1 e2))))))))))
pattern EPrim e = (FixB (CEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Lb (PrimB e)))))))))))
pattern EErr = (FixB (CEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (Rb ErrB))))))))))
