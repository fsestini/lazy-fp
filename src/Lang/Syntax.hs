{-# LANGUAGE DeriveFoldable, GeneralizedNewtypeDeriving, DeriveFunctor,
             StandaloneDeriving, TypeOperators, PatternSynonyms,
             TemplateHaskell #-}

module Lang.Syntax where

import RecursionSchemes
import Data.Set(Set, empty, singleton, union)
import Data.List(nub)
import qualified Data.List.NonEmpty as NE (toList, NonEmpty(..))
import Control.Arrow((&&&))
import AST
import Data.Bifunctor
import Data.Bifunctor.TH
import Data.Bifoldable
import Data.Bitraversable

--------------------------------------------------------------------------------
-- Datatypes for patterns

data Pattern a = PVar a
               | PInt Int
               | PCtor CtorName [Pattern a]
               deriving (Eq, Ord, Show, Functor, Foldable)

instance Traversable Pattern where
  traverse f (PVar x) = PVar <$> f x
  traverse _ (PInt n) = pure $ PInt n
  traverse f (PCtor name ps) = PCtor name <$> sequenceA (map (traverse f) ps)

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
type LangProgram a = [Either DataDecl (LangExpr a)]
type DataDecl = (CtorName, NE.NonEmpty CtorDecl)
type CtorDecl = (CtorName, NE.NonEmpty CtorName)
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

termConstructors :: DataDecl -> [(CtorName, Int)]
termConstructors (_,decls) =
  map (fst &&& (length . snd)) (NE.toList decls) -- TODO: extremely naive. fix

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
