{-# LANGUAGE MultiParamTypeClasses, TypeOperators, KindSignatures,
             TypeSynonymInstances, FlexibleInstances, TemplateHaskell,
             FlexibleContexts, ScopedTypeVariables, GADTs,
             DeriveFunctor, DeriveFoldable, DeriveTraversable, RankNTypes,
             TupleSections #-}

module AST where

import Text.PrettyPrint
import Data.Maybe(isNothing)
import Pair
import Control.Monad (join)
import qualified Data.List.NonEmpty as NE
import qualified Data.Set as S
import Data.Bifunctor
import Data.Bifunctor.TH
import Data.Bifoldable
import Data.Bitraversable
import Data.Comp.Bifun
import MonadVar
import PrettyClass

--------------------------------------------------------------------------------
-- Data types to compose abstract syntax trees

type Name = String
type CtorName = Name
type CtorArity = Int

instance Pair BinderB where
  pFst (BinderB x _) = x
  pSnd (BinderB _ x) = x
  fromPair = uncurry BinderB

data LetMode = NonRecursive | Recursive deriving (Eq, Ord, Show)
data Lit = LInt Int deriving (Show, Eq, Ord)
data PrimOp = Add | Sub | Mul | Eql deriving (Eq, Ord, Show)

data BinderB a b = BinderB a b deriving (Eq, Ord, Show)
data AlterB a b = AlterB CtorName [a] b deriving (Eq, Ord, Show)
data VarB a b = VarB a deriving (Eq, Ord, Show)
data CtorB a b = CtorB CtorName deriving (Eq, Ord, Show)
data LitB a b = LitB Lit deriving (Eq, Ord, Show)
data AppB a b = AppB b b deriving (Eq, Ord, Show)
data LetB a b = LetB LetMode (NE.NonEmpty (BinderB a b)) b
  deriving (Eq, Ord, Show)
data CaseB a b = CaseB b (NE.NonEmpty (AlterB a b)) deriving (Eq, Ord, Show)
data LamB a b = LamB a b deriving (Eq, Ord, Show)
data PrimB a b = PrimB PrimOp deriving (Eq, Ord, Show)
data ErrB a b = ErrB deriving (Eq, Ord, Show)

--------------------------------------------------------------------------------
-- Smart constructors

iApp :: (AppB :<: f) => Term f a -> Term f a -> Term f a
iApp e1 e2 = inject $ AppB e1 e2

iLet :: (LetB :<: f)
     => LetMode
     -> NE.NonEmpty (BinderB a (Term f a))
     -> Term f a
     -> Term f a
iLet m b e = inject $ LetB m b e

--------------------------------------------------------------------------------
-- Instances

$(deriveBifunctor ''BinderB)
$(deriveBifunctor ''AlterB)
$(deriveBifunctor ''VarB)
$(deriveBifunctor ''CtorB)
$(deriveBifunctor ''LitB)
$(deriveBifunctor ''AppB)
$(deriveBifunctor ''LetB)
$(deriveBifunctor ''CaseB)
$(deriveBifunctor ''LamB)
$(deriveBifunctor ''PrimB)
$(deriveBifunctor ''ErrB)
$(deriveBifoldable ''BinderB)
$(deriveBifoldable ''AlterB)
$(deriveBifoldable ''VarB)
$(deriveBifoldable ''CtorB)
$(deriveBifoldable ''LitB)
$(deriveBifoldable ''AppB)
$(deriveBifoldable ''LetB)
$(deriveBifoldable ''CaseB)
$(deriveBifoldable ''LamB)
$(deriveBifoldable ''PrimB)
$(deriveBifoldable ''ErrB)
$(deriveBitraversable ''BinderB)
$(deriveBitraversable ''AlterB)
$(deriveBitraversable ''VarB)
$(deriveBitraversable ''CtorB)
$(deriveBitraversable ''LitB)
$(deriveBitraversable ''AppB)
$(deriveBitraversable ''LetB)
$(deriveBitraversable ''CaseB)
$(deriveBitraversable ''LamB)
$(deriveBitraversable ''PrimB)
$(deriveBitraversable ''ErrB)

--------------------------------------------------------------------------------
-- Utility functions

recNonRec :: LetMode -> a -> a -> a
recNonRec Recursive x _ = x
recNonRec NonRecursive _ x = x

binderBody :: BinderB a b -> b
binderBody (BinderB _ x) = x

binderVar :: BinderB a b -> a
binderVar (BinderB x _) = x

alterBody :: AlterB a b -> b
alterBody (AlterB _ _ x) = x

--------------------------------------------------------------------------------
-- Free variables

monadVarLetTrans :: (MonadVarReader v m, LetB :<: p)
                 => (p v b -> m a) -> p v b -> m a
monadVarLetTrans alg t = case prj t of
  Just (LetB m b e) -> let vars = fmap binderVar b in pushLetVars vars $ alg t
  Nothing -> alg t

monadVarTrans :: forall v m p b a . (MonadVarReader v m, LamB :<: p, LetB :<: p)
              => (p v b -> m a) -> (p v b -> m a)
monadVarTrans alg t = case prj t of
  Just (LamB v _) -> pushLamVar v $ alg t
  Nothing -> case prj t of
    Just (LetB m b e) -> let vars = fmap binderVar b in pushLetVars vars $ alg t
    Nothing -> alg t

isFree :: (MonadVarReader v m, Ord v) => v -> m Bool
isFree x = isNothing . lookupVarEnv x <$> varEnv

freeVarsAlg :: (VarB :<: p, LamB :<: p, LetB :<: p, Ord v, Bifoldable p)
            => p v (S.Set v) -> VarReader v (S.Set v)
freeVarsAlg = monadVarTrans freeVarsAlg'
  where
    freeVarsAlg' :: (VarB :<: p, Ord v, Bifoldable p)
                 => p v (S.Set v) -> VarReader v (S.Set v)
    freeVarsAlg' t = case prj t of
      Just (VarB x) -> do
        b <- isFree x
        if b then return (S.singleton x) else return S.empty
      Nothing -> return $ bifoldr (flip const) S.union S.empty t

freeVars :: (VarB :<: p, LamB :<: p, LetB :<: p, Ord v,
             Bifoldable p, Bitraversable p)
         => Term p v -> S.Set v
freeVars = runEmpty . cataM freeVarsAlg

-- class FreeVars p v where
--   freeVarsAlg :: p v (S.Set w) -> VarReader v (S.Set v)
--
-- instance (FreeVars f v w, FreeVars g v w) => FreeVars (f :+: g) v w where
--   freeVarsAlg f = caseB (freeVarsAlg f) (freeVarsAlg f)
--
-- instance FreeVars VarB v w where
--   freeVarsAlg f (VarB x) = S.singleton (f x)
--
-- instance Ord w => FreeVars AppB v w where
--   freeVarsAlg _ (AppB s1 s2) = S.union s1 s2
--
-- instance Ord w => FreeVars LamB v w where
--   freeVarsAlg f (LamB x s) = s S.\\ S.singleton (f x)
--
-- instance Ord w => FreeVars LetB v w where
--   freeVarsAlg f (LetB m b s) = bFreeVars `S.union` (s `S.difference` binderVars)
--     where
--       binderVars = S.fromList . NE.toList $ fmap (f . binderVar) b
--       bodiesFreeVars = foldr S.union S.empty $ NE.map binderBody b
--       bFreeVars = bodiesFreeVars `S.difference` recNonRec m binderVars S.empty
--
-- instance Ord w => FreeVars CaseB v w where
--   freeVarsAlg f (CaseB s a) =
--     s `S.union` foldr (S.union . afv) S.empty (fmap (bimap f id) a)
--     where afv (AlterB _ vars s') = s' `S.difference` S.fromList vars
--
-- instance Ord w => FreeVars CtorB v w where
--   freeVarsAlg _ (CtorB _) = S.empty
--
-- instance Ord w => FreeVars LitB v w where
--   freeVarsAlg _ (LitB _) = S.empty
--
-- instance Ord w => FreeVars PrimB v w where
--   freeVarsAlg _ (PrimB _) = S.empty
--
-- instance Ord w => FreeVars ErrB v w where
--   freeVarsAlg _ ErrB = S.empty

--------------------------------------------------------------------------------
-- Pretty printing

class PrettySyntax p where
  prettyAlg :: Pretty a => p a Doc -> Doc

instance (PrettySyntax p1, PrettySyntax p2) => PrettySyntax (p1 :+: p2) where
  prettyAlg = caseB prettyAlg prettyAlg

instance PrettySyntax VarB where
  prettyAlg (VarB x) = pPrint x

instance PrettySyntax LitB where
  prettyAlg (LitB (LInt x)) = integer (toInteger x)

instance PrettySyntax CtorB where
  prettyAlg (CtorB name) = pPrint name

instance PrettySyntax AppB where
  prettyAlg (AppB e1 e2) = hsep [parens e1, parens e2]

instance PrettySyntax LetB where
  prettyAlg (LetB m b e) = pLetLetrec m b e

instance PrettySyntax CaseB where
  prettyAlg (CaseB e a) = pCase e a

instance PrettySyntax LamB where
  prettyAlg (LamB x e) = hsep [text "\\", pPrint x, text "->", e]

instance PrettySyntax PrimB where
  prettyAlg (PrimB Add) = text "add#"
  prettyAlg (PrimB Sub) = text "sub#"
  prettyAlg (PrimB Mul) = text "mul#"
  prettyAlg (PrimB Eql) = text "eql#"

instance PrettySyntax ErrB where
  prettyAlg ErrB = text "error#"

pLetLetrec :: Pretty a => LetMode -> NE.NonEmpty (BinderB a Doc) -> Doc -> Doc
pLetLetrec m b e = vcat $ keyword : binders ++ [text "in", nest 2 e]
  where
    keyword = recNonRec m (text "letrec") (text "let")
    binders = NE.toList $ NE.map (nest 2 . pBinder) b
    pBinder (BinderB x e) = hsep [pPrint x, equals, e]

pCase :: Pretty a => Doc -> NE.NonEmpty (AlterB a Doc) -> Doc
pCase e alters =
  vcat $ hsep [text "case", e, text "of"]
       : map (nest 2 . pAlter) (NE.toList alters)
  where
    pAlter (AlterB name vars e) =
      hsep $ pPrint name : map pPrint vars ++ [text "->", e]
