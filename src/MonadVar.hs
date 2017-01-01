{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module MonadVar (
  VarReaderT,
  VarReader,
  VarType(..),
  MonadVarReader(..),
  VarEnv,
  lookupVarEnv,
  pushLetVars,
  runEmptyT,
  runEmpty,
  LamLevel(..),
  LetLevel(..)
) where

import Data.Comp.Bifun
import Control.Monad.Reader
import qualified Data.Map as M
import Control.Monad.Identity
import Utils

data VarType = LamBound Int | LetBound Int
newtype VarEnv v = VarEnv { unVarEnv :: M.Map v VarType }

data LamLevel v = LamLevel Int
data LetLevel v = LetLevel Int

newtype VarReaderT v m a =
  VarReaderT { runVarReaderT :: ReaderT (VarEnv v, LamLevel v, LetLevel v) m a }
  deriving (Functor, Applicative, Monad)

runEmptyT :: VarReaderT v m a -> m a
runEmptyT (VarReaderT reader) = runReaderT reader (VarEnv M.empty, LamLevel $ negate 1, LetLevel $ negate 1)

type VarReader v a = VarReaderT v Identity a

runEmpty :: VarReader v a -> a
runEmpty r = case runEmptyT r of
  (Identity x) -> x

class Monad m => MonadVarReader v m where
  pushLamVar :: v -> m a -> m a
  pushLetVar :: v -> m a -> m a
  varEnv :: m (VarEnv v)
  lamLevel :: m (LamLevel v)
  letLevel :: m (LetLevel v)

pushLetVars :: (MonadVarReader v m, Foldable t) => t v -> m a -> m a
pushLetVars vars m = foldr pushLetVar m vars

lookupVarEnv :: Ord v => v -> VarEnv v -> Maybe VarType
lookupVarEnv v = M.lookup v . unVarEnv

incrLamLevel :: Monad m => VarReaderT v m a -> VarReaderT v m a
incrLamLevel (VarReaderT reader) = VarReaderT $ local lamIncr reader
  where
    lamIncr :: (a,LamLevel v,c) -> (a, LamLevel v, c)
    lamIncr (x,LamLevel l,z) = (x, LamLevel (l + 1), z)

incrLetLevel :: Monad m => VarReaderT v m a -> VarReaderT v m a
incrLetLevel (VarReaderT reader) = VarReaderT $ local letIncr reader
  where
    letIncr :: (a,c, LetLevel v) -> (a, c, LetLevel v)
    letIncr (x, z, LetLevel l) = (x, z, LetLevel (l + 1))

pushLamVarEnv :: Ord v => v -> VarEnv v -> VarEnv v
pushLamVarEnv x = VarEnv . M.insert x (LamBound 0) . fmap incr . unVarEnv
  where
    incr (LamBound i) = LamBound $ i + 1
    incr x = x

firstOf3 :: (a -> d) -> (a,b,c) -> (d,b,c)
firstOf3 f (x,y,z) = (f x, y, z)

sndOf3 :: (a,b,c) -> b
sndOf3 (x,y,z) = y

instance (Ord v, Monad m) => MonadVarReader v (VarReaderT v m) where
  pushLamVar v = VarReaderT . local (firstOf3 $ pushLamVarEnv v) . runVarReaderT
  pushLetVar v = VarReaderT
               . local undefined
               . runVarReaderT
               -- firstOf3 (VarEnv . M.insert v LetBound . unVarEnv)
  varEnv = VarReaderT (fstOf3 <$> ask)
  lamLevel = VarReaderT (sndOf3 <$> ask)
  letLevel = VarReaderT (trd <$> ask)
