module Utils where

import Control.Monad.State
import Data.List.NonEmpty

chunkBy :: (a -> a -> Bool) -> [a] -> [[a]]
chunkBy _ [] = []
chunkBy p (x:xs) = evalState aux (x :| [], xs)
  where
    aux = do
      state <- get
      let remaining = snd state
          current = fst state
      case remaining of
        [] -> return [toList current]
        (x:xs) -> case current of
          (y :| ys) -> if p x y
            then put (y :| ys ++ [x], xs) >> aux
            else (:) (toList (y :| ys)) <$> (put (x :| [], xs) >> aux)

fixpoint :: Eq a => a -> (a -> a) -> a
fixpoint x f = let y = f x in if x == y then x else fixpoint y f

fstOf3 :: (a,b,c) -> a
fstOf3 (x,_,_) = x

thirdOf3 :: (a,b,c) -> c
thirdOf3 (_,_,x) = x

third :: (c -> d) -> (a, b, c) -> (a, b, d)
third f (x,y,z) = (x,y,f z)

second' :: (b -> b -> c) -> (a,b) -> (a,b) -> c
second' f (_,i) (_,j) = f i j

secondM :: Monad m => (b -> m d) -> (a,b) -> m (a,d)
secondM f (x,y) = (,) x <$> f y

thirdM :: Monad m => (c -> m d) -> (a,b,c) -> m (a,b,d)
thirdM f (x,y,z) = (,,) x y <$> f z
