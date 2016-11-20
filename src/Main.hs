import GMachine.Main

import System.IO

main :: IO ()
main = do
  str <- readAll
  putStrLn . runShow . concat $ interleave str " ; "

readAll :: IO [String]
readAll = do
  b <- isEOF
  if b
    then return []
    else do
      line <- getLine
      rest <- readAll
      return $ line : rest

interleave :: [a] -> a -> [a]
interleave [] _ = []
interleave [x] _ = [x]
interleave (x : y : xs) p = x : p : interleave (y : xs) p
