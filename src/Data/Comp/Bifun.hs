{-# LANGUAGE DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             UndecidableInstances, MultiParamTypeClasses,
             FlexibleInstances, ConstraintKinds, FlexibleContexts,
             ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Data.Comp.Bifun (
    (:+:)(..)
  , (:*:)(..)
  , (:<:)
  , (:=:)
  , inj
  , prj
  , inject
  , cata
  , para
  , cataM
  , split
  , Term(..)
  , caseB
  ) where

import Control.Monad
import Data.Proxy
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Prelude hiding (Left, Right)

data Pos = Here | Left Pos | Right Pos
data Res = Found Pos | NotFound | Ambiguous

infixr 5 :+:
data (f :+: g) a b = Inl (f a b) | Inr (g a b)

type family Elem (e :: * -> * -> *) (p :: * -> * -> *) :: Res where
  Elem e e = Found Here
  Elem e (l :+: r) = Choose (Elem e l) (Elem e r)
  Elem e p = NotFound

type family Choose (l :: Res) (r :: Res) :: Res where
  Choose (Found x) (Found y) = Ambiguous
  Choose Ambiguous y = Ambiguous
  Choose x Ambiguous = Ambiguous
  Choose (Found x) y = Found (Left x)
  Choose x (Found y) = Found (Right y)
  Choose x y = NotFound

-- Support for non-atomic signatures
data Struc = Sum Struc Struc | Atom Res

type family GetStruc f g :: Struc where
  GetStruc (f1 :+: f2) g = Sum (GetStruc f1 g) (GetStruc f2 g)
  GetStruc f g = Atom (Elem f g)

-- Subsumption type class for atomic signatures
class Subsume (res :: Res) f g where
  inj' :: Proxy res -> f a b -> g a b
  prj' :: Proxy res -> g a b -> Maybe (f a b)

instance Subsume (Found Here) f f where
  inj' _ = id
  prj' _ = Just

instance Subsume (Found p) f l => Subsume (Found (Left p)) f (l :+: r) where
  inj' _ = Inl . inj' (Proxy :: Proxy (Found p))
  prj' _ (Inl x) = prj' (Proxy :: Proxy (Found p)) x
  prj' _ (Inr _) = Nothing

instance Subsume (Found p) f r => Subsume (Found (Right p)) f (l :+: r) where
  inj' _ = Inr . inj' (Proxy :: Proxy (Found p))
  prj' _ (Inr x) = prj' (Proxy :: Proxy (Found p)) x
  prj' _ (Inl _) = Nothing

-- Subsumption type class for arbitrary signatures
class Subsume' (s :: Struc) f g where
  inj'' :: Proxy s -> f a b -> g a b
  prj'' :: Proxy s -> g a b -> Maybe (f a b)

instance Subsume res f g => Subsume' (Atom res) f g where
  inj'' _ = inj' (Proxy :: Proxy res)
  prj'' _ = prj' (Proxy :: Proxy res)

instance (Subsume' s1 f1 g, Subsume' s2 f2 g)
  => Subsume' (Sum s1 s2) (f1 :+: f2) g where
  inj'' _ (Inl x) = inj'' (Proxy :: Proxy s1) x
  inj'' _ (Inr x) = inj'' (Proxy :: Proxy s2) x
  prj'' _ x = case prj'' (Proxy :: Proxy s1) x of
    Just y -> Just (Inl y)
    _      -> case prj'' (Proxy :: Proxy s2) x of
                Just y  -> Just (Inr y)
                Nothing -> Nothing

--------------------------------------------------------------------------------
-- Signature subsumption constraint, with injection and projection functions

type f :<: g = Subsume' (GetStruc f g) f g

inj :: forall f g a b . (f :<: g) => f a b -> g a b
inj = inj'' (Proxy :: Proxy (GetStruc f g))

prj :: forall f g a b . (f :<: g) => g a b -> Maybe (f a b)
prj = prj'' (Proxy :: Proxy (GetStruc f g))

inject :: (g :<: f) => g a (Term f a) -> Term f a
inject = Term . inj

--------------------------------------------------------------------------------
-- Signature isomorphism

infix 4 :=:
type f :=: g = (f :<: g, g :<: f)

--------------------------------------------------------------------------------
-- Bifunctor fixpoints

newtype Term (p :: * -> * -> *) (a :: *) = Term { unTerm :: p a (Term p a) }

instance (Bifunctor f, Bifunctor g) => Bifunctor (f :+: g) where
  bimap f g (Inl x) = Inl $ bimap f g x
  bimap f g (Inr x) = Inr $ bimap f g x

instance (Bifoldable f, Bifoldable g) => Bifoldable (f :+: g) where
  bifoldr f g z (Inl x) = bifoldr f g z x
  bifoldr f g z (Inr x) = bifoldr f g z x

instance (Bitraversable f, Bitraversable g) => Bitraversable (f :+: g) where
  bitraverse f g (Inl x) = Inl <$> bitraverse f g x
  bitraverse f g (Inr x) = Inr <$> bitraverse f g x

instance (Bifunctor f1, Bifunctor f2) => Bifunctor (f1 :*: f2) where
  bimap f g (x1 :*: x2) = bimap f g x1 :*: bimap f g x2

instance (Bifoldable f1, Bifoldable f2) => Bifoldable (f1 :*: f2) where
  bifoldr f g z (x1 :*: x2) = bifoldr f g (bifoldr f g z x2) x1

instance (Bitraversable f1, Bitraversable f2) => Bitraversable (f1 :*: f2) where
  bitraverse f g (x1 :*: x2) = (:*:) <$> bitraverse f g x1 <*> bitraverse f g x2

instance {-# OVERLAPS #-} (Bifunctor f) => Functor (f a) where
  fmap = bimap id

instance {-# OVERLAPS #-} (Bifoldable f) => Foldable (f a) where
  foldr = bifoldr (const id)

instance {-# OVERLAPS #-} (Bitraversable f) => Traversable (f a) where
  sequenceA = bisequenceA . first pure

instance Bifunctor p => Functor (Term p) where
  fmap f (Term t) = Term $ bimap f (fmap f) t

instance Bifoldable p => Foldable (Term p) where
  foldr f z (Term t) = bifoldr f (flip (foldr f)) z t

instance (Eq (p a b), Eq (q a b)) => Eq ((p :+: q) a b) where
  Inl t1 == Inl t2 = t1 == t2
  Inl _ == Inr _ = False
  Inr _ == Inl _ = False
  Inr t1 == Inr t2 = t1 == t2

--------------------------------------------------------------------------------
-- Utility functions

cata :: Bifunctor p => (p a b -> b) -> Term p a -> b
cata alg = alg . second (cata alg) . unTerm

cataM :: (Bitraversable f, Monad m) => (f a b -> m b) -> Term f a -> m b
cataM algM (Term t) = algM <=< bimapM return (cataM algM) $ t

split :: (f :=: f1 :+: f2) => (f1 x a -> b) -> (f2 x a -> b) -> f x a -> b
split f1 f2 x = case inj x of
  Inl y -> f1 y
  Inr y -> f2 y

caseB :: (p a b -> c) -> (q a b -> c) -> (p :+: q) a b -> c
caseB alg1 alg2 (Inl x) = alg1 x
caseB alg1 alg2 (Inr x) = alg2 x

splitAlg :: forall f f1 f2 a b .
          (f :=: (f1 :+: f2), Bifunctor f, Bifunctor f1, Bifunctor f2)
         => (f1 a b -> b) -> (f2 a b -> b) -> Term f a -> b
splitAlg f g (Term t) = split f' g' t
  where
    f' = f . second (splitAlg f g)
    g' = g . second (splitAlg f g)

-- paraSplitM :: (f :=: f1 :+: f2, Bifunctor f,
--                Bitraversable f1, Bitraversable f2, Monad m)
--      => (forall a b . f1 a b -> f a b) -> (forall a b . f2 a b -> f a b)
--      -> (f1 a (Term f a, b) -> m b) -> (f2 a (Term f a, b) -> m b)
--      -> Term f a -> m b
-- paraSplitM alg1 alg2 alg3 alg4 t = undefined

para :: (Bifunctor f) => (f a (Term f a, b) -> b)
                      -> Term f a -> b
para f = snd . cata run
  where run t = (Term $ second fst t, f t)

paraM :: (Bitraversable f, Monad m) =>
         (f a (Term f a, b) -> m b) -> Term f a -> m b
paraM f = fmap snd . cataM run
    where run t = do
            a <- f t
            return (Term $ second fst t, a)

--------------------------------------------------------------------------------
-- Products

data (f :*: g) a b = (f a b) :*: (g a b)
