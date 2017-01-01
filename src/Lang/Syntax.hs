{-# LANGUAGE DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving,
             DeriveFunctor, StandaloneDeriving, TypeOperators, PatternSynonyms,
             TemplateHaskell #-}

module Lang.Syntax where

import RecursionSchemes
import Data.Set(Set, empty, singleton, union)
import Data.List(nub)
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

newtype LangExprBase a b = LEB ((
    VarB :++: CtorB :++: LamB :++: PatternLetB :++: CaseB :++: AppB
    :++: LitB :++: PrimB) a b) deriving (Bifunctor, Bifoldable)

instance Bitraversable LangExprBase where
  bitraverse f g (LEB t) = LEB <$> bitraverse f g t

type LangExpr = FixB LangExprBase
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
allVars = foldr union empty . fmap singleton

--------------------------------------------------------------------------------
-- Pattern synonyms

pattern LVarF e = (LEB (Lb (VarB e)))
pattern LCtorF e = (LEB (Rb (Lb (CtorB e))))
pattern LLamF x e = (LEB (Rb (Rb (Lb (LamB x e)))))
pattern LLetF e1 e2 e3 = (LEB (Rb (Rb (Rb (Lb (PLetB e1 e2 e3))))))
pattern LCaseF e1 e2 = (LEB (Rb (Rb (Rb (Rb (Lb (CaseB e1 e2)))))))
pattern LAppF e1 e2 = (LEB (Rb (Rb (Rb (Rb (Rb (Lb (AppB e1 e2))))))))
pattern LLitF e = (LEB (Rb (Rb (Rb (Rb (Rb (Rb (Lb (LitB e)))))))))
pattern LPrimF e = (LEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (PrimB e)))))))))

pattern LVarFB e = (LEB (Lb e))
pattern LCtorFB e = (LEB (Rb (Lb e)))
pattern LLamFB e = (LEB (Rb (Rb (Lb e))))
pattern LLetFB e = (LEB (Rb (Rb (Rb (Lb e)))))
pattern LCaseFB e = (LEB (Rb (Rb (Rb (Rb (Lb e))))))
pattern LAppFB e = (LEB (Rb (Rb (Rb (Rb (Rb (Lb e)))))))
pattern LLitFB e = (LEB (Rb (Rb (Rb (Rb (Rb (Rb (Lb e))))))))
pattern LPrimFB e = (LEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb e))))))))

pattern LVar e = (FixB (LEB (Lb (VarB e))))
pattern LCtor e = (FixB (LEB (Rb (Lb (CtorB e)))))
pattern LLam x e = (FixB (LEB (Rb (Rb (Lb (LamB x e))))))
pattern LLet e1 e2 e3 = (FixB (LEB (Rb (Rb (Rb (Lb (PLetB e1 e2 e3)))))))
pattern LCase e1 e2 = (FixB (LEB (Rb (Rb (Rb (Rb (Lb (CaseB e1 e2))))))))
pattern LApp e1 e2 = (FixB (LEB (Rb (Rb (Rb (Rb (Rb (Lb (AppB e1 e2)))))))))
pattern LLit e = (FixB (LEB (Rb (Rb (Rb (Rb (Rb (Rb (Lb (LitB e))))))))))
pattern LPrim e = (FixB (LEB (Rb (Rb (Rb (Rb (Rb (Rb (Rb (PrimB e))))))))))
