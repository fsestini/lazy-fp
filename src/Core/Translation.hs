{-# LANGUAGE TypeOperators, LambdaCase, ScopedTypeVariables #-}

module Core.Translation where

import AST
import Data.Comp.Bifun
import Control.Monad.Reader
import Control.Monad.State
import Data.Set as S (toList)
import Utils
import Control.Monad
import PickFresh
import Lang.Syntax as L
import Core.Syntax
import qualified Data.List.NonEmpty as NE
import Lang.PatternCompiler
import Types.DataDecl

type LangExprBRest =
  VarB :+: CtorB :+: LamB :+: CaseB :+: AppB :+: LitB :+: PrimB

translateSc :: (Show a, Ord a, PickFresh a)
            => [DataDecl a] -- TODO: this type var should probably be different
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

translateToCoreM :: forall a . (Show a, Eq a, PickFresh a)
                 => LangExpr a
                 -> PMMonad a (CoreExpr a)
translateToCoreM = cataM $ split alg1 alg2
  where
    alg1 (PLetB m b e) = do
      transl <- matchLetBinders . NE.toList $ b
      return $ ELet m (NE.fromList transl) e
    alg2 :: LangExprBRest a (CoreExpr a) -> PMMonad a (CoreExpr a)
    alg2 = return . inject

-- Old version:
-- translateToCoreM :: (Show a, Eq a, PickFresh a)
--                  => LangExpr a
--                  -> PMMonad a (CoreExpr a)
-- translateToCoreM = cata $ \case
--   (LLetF m b e) -> do
--     coredBinders <- forM b sequence
--     translatedBinders <- matchLetBinders (NE.toList coredBinders)
--     let b' = head translatedBinders :| tail translatedBinders
--     ELet m b' <$> e
--   (LVarFB e)  -> seqfix . CEB . inj $ e
--   (LCtorFB e) -> seqfix . CEB . inj $ e
--   (LLamFB e)  -> seqfix . CEB . inj $ e
--   (LCaseFB e) -> seqfix . CEB . inj $ e
--   (LAppFB e)  -> seqfix . CEB . inj $ e
--   (LLitFB e)  -> seqfix . CEB . inj $ e
--   (LPrimFB e) -> seqfix . CEB . inj $ e
