{-# LANGUAGE MultiParamTypeClasses, TypeOperators, KindSignatures,
             TypeSynonymInstances, FlexibleInstances, TemplateHaskell #-}

module AST where

import Pair
import qualified Data.List.NonEmpty as NE
import qualified Data.Set as S
import Data.Bifunctor
import Data.Bifunctor.TH
import Data.Bifoldable
import Data.Bitraversable

--------------------------------------------------------------------------------
-- Sum of bifunctors

data (:++:) f g (a :: *) (b :: *) = Lb (f a b) | Rb (g a b)
  deriving (Eq, Ord, Show)
infixr 5 :++:

instance (Bifunctor f, Bifunctor g) => Bifunctor ((:++:) f g) where
  bimap f g (Lb x) = Lb $ bimap f g x
  bimap f g (Rb x) = Rb $ bimap f g x

instance (Bifoldable f, Bifoldable g) => Bifoldable (f :++: g) where
  bifoldr f g z (Lb x) = bifoldr f g z x
  bifoldr f g z (Rb x) = bifoldr f g z x

instance (Bitraversable t1, Bitraversable t2)
  => Bitraversable (t1 :++: t2) where
  bitraverse f g (Lb x) = Lb <$> bitraverse f g x
  bitraverse f g (Rb x) = Rb <$> bitraverse f g x

--------------------------------------------------------------------------------
-- Data types to compose abstract syntax trees

type Name = String
type CtorName = Name
type CtorArity = Int

data BinderB a b = BinderB a b deriving (Eq, Ord, Show)
$(deriveBifunctor ''BinderB)
$(deriveBifoldable ''BinderB)
$(deriveBitraversable ''BinderB)

data AlterB a b = AlterB CtorName [a] b deriving (Eq, Ord, Show)
$(deriveBifunctor ''AlterB)
$(deriveBifoldable ''AlterB)
$(deriveBitraversable ''AlterB)

instance Pair BinderB where
  pFst (BinderB x _) = x
  pSnd (BinderB _ x) = x
  fromPair = uncurry BinderB

data LetMode = NonRecursive | Recursive deriving (Eq, Ord, Show)
data Lit = LInt Int deriving (Show, Eq, Ord)
data PrimOp = Add | Sub | Mul | Eql deriving (Eq, Ord, Show)

data VarB a b = VarB a deriving (Eq, Ord, Show)
$(deriveBifunctor ''VarB)
$(deriveBifoldable ''VarB)
$(deriveBitraversable ''VarB)

data CtorB a b = CtorB CtorName deriving (Eq, Ord, Show)
$(deriveBifunctor ''CtorB)
$(deriveBifoldable ''CtorB)
$(deriveBitraversable ''CtorB)

data LitB a b = LitB Lit deriving (Eq, Ord, Show)
$(deriveBifunctor ''LitB)
$(deriveBifoldable ''LitB)
$(deriveBitraversable ''LitB)

data AppB a b = AppB b b deriving (Eq, Ord, Show)
$(deriveBifunctor ''AppB)
$(deriveBifoldable ''AppB)
$(deriveBitraversable ''AppB)

data LetB a b = LetB LetMode (NE.NonEmpty (BinderB a b)) b
  deriving (Eq, Ord, Show)
$(deriveBifunctor ''LetB)
$(deriveBifoldable ''LetB)
$(deriveBitraversable ''LetB)

data CaseB a b = CaseB b (NE.NonEmpty (AlterB a b)) deriving (Eq, Ord, Show)
$(deriveBifunctor ''CaseB)
$(deriveBifoldable ''CaseB)
$(deriveBitraversable ''CaseB)

data LamB a b = LamB a b deriving (Eq, Ord, Show)
$(deriveBifunctor ''LamB)
$(deriveBifoldable ''LamB)
$(deriveBitraversable ''LamB)

data PrimB a b = PrimB PrimOp deriving (Eq, Ord, Show)
$(deriveBifunctor ''PrimB)
$(deriveBifoldable ''PrimB)
$(deriveBitraversable ''PrimB)

data ErrB a b = ErrB deriving (Eq, Ord, Show)
$(deriveBifunctor ''ErrB)
$(deriveBifoldable ''ErrB)
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
-- Injections

class (Bifunctor sub, Bifunctor sup) => sub :<: sup where
  inj :: sub a b -> sup a b

instance {-# OVERLAPPABLE #-} Bifunctor f => f :<: f where
  inj = id

instance {-# OVERLAPPABLE #-} (Bifunctor f, Bifunctor g)
  => f :<: (f :++: g) where
  inj = Lb

instance {-# OVERLAPPABLE #-} (Bifunctor f, Bifunctor g, Bifunctor h, f :<: g)
  => f :<: (h :++: g) where
  inj = Rb . inj
