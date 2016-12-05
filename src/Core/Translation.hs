{-# LANGUAGE ScopedTypeVariables #-}

module Core.Translation where

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
  matched <- match lambdaVars translated EError
  return $ foldr ELam matched lambdaVars
  where
    noOfPatterns = length . fst . head $ things

translateToCoreM :: (Show a, Eq a, PickFresh a) => LangExpr a -> PMMonad a (CoreExpr a)
translateToCoreM (Let m b e) = do
  coredBinders <- forM b (secondM translateToCoreM)
  translatedBinders <- matchLetBinders (NE.toList coredBinders)
  translatedBody <- translateToCoreM e
  let b' = head translatedBinders :| tail translatedBinders
  return $ ELet m b' translatedBody
translateToCoreM (Var x) = return $ EVar x
translateToCoreM (Ctor name) = return $ ECtor name
translateToCoreM (Lam xs e) = do
  tr <- translateToCoreM e
  return $ foldr ELam tr xs
translateToCoreM (Case e a) = ECase <$> translateToCoreM e
                                    <*> forM a (thirdM translateToCoreM)
translateToCoreM (App e1 e2) = EAp <$> translateToCoreM e1
                                   <*> translateToCoreM e2
translateToCoreM (Lit (LInt n)) = return $ ENum n
translateToCoreM (PrimOp p) = return $ EPrimitive p
