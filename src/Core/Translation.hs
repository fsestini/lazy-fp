{-# LANGUAGE LambdaCase, ScopedTypeVariables #-}

module Core.Translation where

import AST
import RecursionSchemes
import Control.Monad.Reader
import Control.Monad.State
import Data.Set as S (toList)
import Utils
import Control.Monad
import PickFresh
import Lang.Syntax as L
import Core.Syntax
import Data.List.NonEmpty as NE (NonEmpty(..), toList)
import Lang.PatternCompiler

translateSc :: (Show a, Ord a, PickFresh a)
            => [DataDecl]
            -> [([Pattern a], LangExpr a)]
            -> CoreExpr a
translateSc decls things =
  evalState (runReaderT (translateScM things) decls) totalVars
  where
    totalVars = concatMap patternFreeVars (concatMap fst things)
             ++ concatMap ((S.toList . L.allVars) . snd) things

translateScM :: forall a . (Show a, Ord a, PickFresh a)
             => [([Pattern a], LangExpr a)]
             -> PMMonad a (CoreExpr a)
translateScM things = do
  translated <- forM things (secondM translateToCoreM)
  lambdaVars <- pickNFresh noOfPatterns
  matched <- match lambdaVars translated EErr
  return $ foldr ELam matched lambdaVars
  where
    noOfPatterns = length . fst . head $ things

translateToCoreM :: (Show a, Eq a, PickFresh a)
                 => LangExpr a
                 -> PMMonad a (CoreExpr a)
translateToCoreM = cata $ \case
  (LLetF m b e) -> do
    coredBinders <- forM b sequence
    translatedBinders <- matchLetBinders (NE.toList coredBinders)
    let b' = head translatedBinders :| tail translatedBinders
    ELet m b' <$> e
  (LVarFB e)  -> seqfix . CEB . inj $ e
  (LCtorFB e) -> seqfix . CEB . inj $ e
  (LLamFB e)  -> seqfix . CEB . inj $ e
  (LCaseFB e) -> seqfix . CEB . inj $ e
  (LAppFB e)  -> seqfix . CEB . inj $ e
  (LLitFB e)  -> seqfix . CEB . inj $ e
  (LPrimFB e) -> seqfix . CEB . inj $ e
