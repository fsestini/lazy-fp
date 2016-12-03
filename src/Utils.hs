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
