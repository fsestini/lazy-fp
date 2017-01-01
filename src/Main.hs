{-# LANGUAGE ScopedTypeVariables #-}

import Debug.Trace
import Control.Monad.Except
import GMachine.Main
import Core.DependencyAnalysis
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
import AST
import Types.Inference
import Types.Schemes
import Types.DataDecl

---

main :: IO ()
main = do
  str <- readAll
  putStrLn . runShow . concat $ interleave str " ; "

getCoreScs :: FilePath -> IO [CoreScDefn String]
getCoreScs filePath = do
  file <- readFile filePath
  let (dataDecls, chunked) = parseAndChunk file
      coreScs = map (uncurry (toCoreSc dataDecls)) chunked
  return coreScs

printTypedCore :: FilePath -> IO ()
printTypedCore filePath = do
  file <- readFile filePath
  let (dataDecls, chunked) = parseAndChunk file
      coreScs = map (uncurry (toCoreSc dataDecls)) chunked
  case runExcept $ inferCoreScDefns dataDecls coreScs of
    (Left x) -> putStrLn $ "error: " ++ x
    (Right things) -> forM_ things $ \((name, e), ty :: TypeScheme String) -> do
      putStrLn $ name ++ " : " ++ show ty
      putStrLn $ name ++ " = " ++ render (pExpr e)

printCoreRepr :: FilePath -> IO ()
printCoreRepr filePath = do
  file <- readFile filePath
  let (dataDecls, chunked) = parseAndChunk file
      coreScs = map (uncurry (toCoreSc dataDecls)) chunked
  forM_ coreScs $ \(name, e) -> putStrLn $ name ++ " = " ++ render (pExpr e)

toCoreSc :: [DataDecl String]
         -> String
         -> [([Pattern String], LangExpr String)]
         -> CoreScDefn String
toCoreSc datadecls scName defn =
  (scName, depAnalysisTrans $ translateSc datadecls defn)

parseAndChunk :: String
              -> ([DataDecl String], [(String, [([Pattern String], LangExpr String)])])
parseAndChunk text = (dataDecls, chunkByName scDecls)
  where (dataDecls, scDecls) =
          partitionEithers . parseProgram . scanTokens $ text

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
