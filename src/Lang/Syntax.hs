{-# LANGUAGE DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving,
             DeriveFunctor, StandaloneDeriving, TypeOperators, PatternSynonyms,
             TemplateHaskell, LiberalTypeSynonyms #-}

module Lang.Syntax where

import Data.Comp.Bifun
import Data.Set(Set, empty, singleton, union)
import Data.List(nub, union)
import qualified Data.List.NonEmpty as NE (toList, NonEmpty(..))
import Control.Arrow((&&&))
import AST
import Types.DataDecl
import Types.Schemes
import Data.Bifunctor
import Data.Bifunctor.TH
import Data.Bifoldable
import Data.Bitraversable

--------------------------------------------------------------------------------
-- Datatypes for patterns

data Pattern a = PVar a
               | PInt Int
               | PCtor CtorName [Pattern a]
               deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data PatternBinderB a b = PBinderB (Pattern a) b deriving (Eq, Ord, Show)
$(deriveBifunctor ''PatternBinderB)
$(deriveBifoldable ''PatternBinderB)
$(deriveBitraversable ''PatternBinderB)

data PatternLetB a b = PLetB LetMode (NE.NonEmpty (PatternBinderB a b)) b
  deriving (Eq, Ord, Show)
$(deriveBifunctor ''PatternLetB)
$(deriveBifoldable ''PatternLetB)
$(deriveBitraversable ''PatternLetB)

--------------------------------------------------------------------------------
-- Main types for expressions

type LangExprB = VarB :+: CtorB :+: LamB :+: PatternLetB :+: CaseB
                 :+: AppB :+: LitB :+: PrimB

-- instance Bitraversable LangExprBase where
--   bitraverse f g () =  <$ itraverse f g t

type LangExpr = Term LangExprB
-- TODO: LangProgram should probably be a bifunctor: LangProgram a v
type LangProgram a = [Either (DataDecl a) (LangExpr a)]
type LangAlter a = AlterB a (LangExpr a)
type ScDefn a = (a, [Pattern a], LangExpr a)

--------------------------------------------------------------------------------
-- Utility functions -- a bit messy, TODO: fix

scName :: ScDefn a -> a
scName (x,_,_) = x

getScNames :: Eq a => [ScDefn a] -> [a]
getScNames defns = nub $ map scName defns

chunkByName :: Eq a => [ScDefn a] -> [(a, [([Pattern a], LangExpr a)])]
chunkByName defns = flip map names $ \name ->
  (name, map (\(_,y,z) -> (y,z)) $ filter ((== name) . scName) defns)
  where
    names = getScNames defns

-- TODO: extremely naive. fix
termConstructors :: DataDecl a -> [(CtorName, Int)]
termConstructors (_, _, decls) =
  map (fst &&& (schemeArity . snd)) (NE.toList decls)

patternFreeVars :: Pattern a -> [a]
patternFreeVars = foldr (:) []

allVars :: Ord a => LangExpr a -> Set a
allVars = foldr Data.Set.union empty . fmap singleton

--------------------------------------------------------------------------------
-- Pattern synonyms

pattern LVarF e = (Inl (VarB e))
pattern LCtorF e = (Inr (Inl (CtorB e)))
pattern LLamF x e = (Inr (Inr (Inl (LamB x e))))
pattern LLetF e1 e2 e3 = (Inr (Inr (Inr (Inl (PLetB e1 e2 e3)))))
pattern LCaseF e1 e2 = (Inr (Inr (Inr (Inr (Inl (CaseB e1 e2))))))
pattern LAppF e1 e2 = (Inr (Inr (Inr (Inr (Inr (Inl (AppB e1 e2)))))))
pattern LLitF e = (Inr (Inr (Inr (Inr (Inr (Inr (Inl (LitB e))))))))
pattern LPrimF e = (Inr (Inr (Inr (Inr (Inr (Inr (Inr (PrimB e))))))))

pattern LVar e = (Term (Inl (VarB e)))
pattern LCtor e = (Term (Inr (Inl (CtorB e))))
pattern LLam x e = (Term (Inr (Inr (Inl (LamB x e)))))
pattern LLet e1 e2 e3 = (Term (Inr (Inr (Inr (Inl (PLetB e1 e2 e3))))))
pattern LCase e1 e2 = (Term (Inr (Inr (Inr (Inr (Inl (CaseB e1 e2)))))))
pattern LApp e1 e2 =
  (Term (Inr (Inr (Inr (Inr (Inr (Inl (AppB e1 e2))))))))
pattern LLit e = (Term (Inr (Inr (Inr (Inr (Inr (Inr (Inl (LitB e)))))))))
pattern LPrim e =
  (Term (Inr (Inr (Inr (Inr (Inr (Inr (Inr (PrimB e)))))))))
