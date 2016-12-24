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
import Data.Functor.Foldable

data FixB f a = FixB { unFixB :: f a (FixB f a) }

type instance Base (FixB f a) = f a

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
