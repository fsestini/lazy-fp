module Utils where

import Control.Monad.State
import qualified Data.List.NonEmpty as NE
import Data.Maybe(fromMaybe)
import Data.Functor.Compose
import qualified Data.Set as S
import Data.Foldable

fromMaybe' = flip fromMaybe

chunkBy :: (a -> a -> Bool) -> [a] -> [[a]]
chunkBy _ [] = []
chunkBy p (x:xs) = evalState aux (x NE.:| [], xs)
  where
    aux = do
      state <- get
      let remaining = snd state
          current = fst state
      case remaining of
        [] -> return [NE.toList current]
        (x:xs) -> case current of
          (y NE.:| ys) -> if p x y
            then put (y NE.:| ys ++ [x], xs) >> aux
            else (:) (toList (y NE.:| ys)) <$> (put (x NE.:| [], xs) >> aux)

fixpoint :: Eq a => a -> (a -> a) -> a
fixpoint x f = let y = f x in if x == y then x else fixpoint y f

fstOf3 :: (a,b,c) -> a
fstOf3 (x,_,_) = x

thirdOf3 :: (a,b,c) -> c
thirdOf3 (_,_,x) = x

dropThird :: (a,b,c) -> (a,b)
dropThird (x,y,z) = (x,y)

third :: (c -> d) -> (a, b, c) -> (a, b, d)
third f (x,y,z) = (x,y,f z)

second' :: (b -> b -> c) -> (a,b) -> (a,b) -> c
second' f (_,i) (_,j) = f i j

secondM :: Monad m => (b -> m d) -> (a,b) -> m (a,d)
secondM f (x,y) = (,) x <$> f y

secondAC :: (Applicative g) => (b -> Compose g f c) -> (a,b) -> g (a, f c)
secondAC nt (x,y) = (,) x <$> (getCompose . nt $ y)

thirdM :: Monad m => (c -> m d) -> (a,b,c) -> m (a,b,d)
thirdM f (x,y,z) = (,,) x y <$> f z

fromFoldable :: (Ord a, Foldable f) => f a -> S.Set a
fromFoldable = S.fromList . toList
