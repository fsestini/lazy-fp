{-# LANGUAGE ScopedTypeVariables, TypeFamilies, FlexibleInstances,
             FlexibleContexts #-}

{- Re-exports types and functions from the package recursion-schemes,
   with some additions.
-}

module RecursionSchemes(
  Base,
  Fix(..),
  FixB(..),
  Recursive(..),
  hylo,
  seqfix
) where

import Data.Bitraversable
import Data.Bifunctor
import Data.Bifoldable
-- import Data.Functor.Foldable

data FixB f a = FixB { unFixB :: f a (FixB f a) }

type family Base (t :: *) :: * -> *
type instance Base (FixB f a) = f a

class Functor (Base t) => Recursive t where
  project :: t -> Base t t
  cata :: (Base t a -> a) -- ^ a (Base t)-algebra
       -> t               -- ^ fixed point
       -> a               -- ^ result
  cata f = c where c = f . fmap c . project

  para :: (Base t (t, a) -> a) -> t -> a
  para t = p where p x = t . fmap ((,) <*> p) $ project x

hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo f g = h where h = f . fmap h . g

newtype Fix f = Fix (f (Fix f))

instance {-# OVERLAPS #-} (Bifunctor f) => Functor (f a) where
  fmap = bimap id

instance (Bifoldable f) => Foldable (f a) where
  foldr = bifoldr (const id)

instance (Bitraversable f) => Traversable (f a) where
  sequenceA = bisequenceA . bimap pure id

instance (Bifunctor f) => Recursive (FixB f a) where
  project = unFixB

instance (Bifunctor f) => Functor (FixB f) where
  fmap g = FixB . bimap g (fmap g) . unFixB

instance (Bifoldable f) => Foldable (FixB f) where
  foldr g z (FixB x) = bifoldr g (flip (foldr g)) z x

seqfix :: (Bitraversable f, Applicative m) => f a (m (FixB f a)) -> m (FixB f a)
seqfix = fmap FixB . bisequenceA . bimap pure id
