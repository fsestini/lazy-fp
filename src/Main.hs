import GMachine.Main

import Control.Monad.Reader
import Control.Monad.State
import Data.List.NonEmpty(NonEmpty(..))
import Core.Syntax
import Control.Arrow(second)
import Text.PrettyPrint
import Data.Either
import Lang.Parser
import Lang.Lexer
import Lang.Syntax
import System.IO
import Control.Monad
import Lang.PatternCompiler
import Core.Pretty
import Core.Translation

---

str = "data Nat where\n  Zero : Nat ;\n  Succ : Nat -> Nat\n\n%\n\nf Zero = 10\n%\nf (Succ n) = 20\n\n%\n\nmain = 30\n"

dataDecls = fst . partitionEithers . parseProgram . scanTokens $ str
scDecls = snd . partitionEithers . parseProgram . scanTokens $ str
chunked = chunkByName scDecls

azdazd name stuff = do
  let e = translateSc dataDecls stuff
  putStrLn $ name ++ " = " ++ render (pExpr e)

stuffOfF = snd $ head chunked

translated :: [Equation String]
translated = map (second translateToCore) stuffOfF

(Just ctorEqs) = allStartWithCtor translated
groups = groupByCtor ctorEqs
definedAlters = mapM (groupToAlter ["y"] EError) groups

m = ctorRule ("x" :| []) translated ctorEqs EError
(ECase e a) = evalState (runReaderT m dataDecls) ["n"]

---


main :: IO ()
main = do
  str <- readAll
  putStrLn . runShow . concat $ interleave str " ; "

printCoreRepr :: FilePath -> IO ()
printCoreRepr filePath = do
  file <- readFile filePath
  let (dataDecls, scDecls) = partitionEithers . parseProgram . scanTokens $ file
      chunked = chunkByName scDecls
  forM_ chunked $ \(name, stuff) -> do
    let e = translateSc dataDecls stuff
    putStrLn $ name ++ " = " ++ render (pExpr e)

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
