
module Types.Unification(
  UnifEquation,
  UnifRes,
  unifySet
) where

import Data.Tuple(swap)
import Types.Schemes (TySubst(..), Type, Monotype (..), subType, deltaSub, occurs)
import Control.Monad.Except
import Control.Category (Category(..))
import Prelude hiding ((.), id)

type UnifRes a = Except String a
type UnifEquation a = (Type a, Type a)

flipEq :: UnifEquation a -> UnifEquation a
flipEq = swap

extend :: Ord a => TySubst a a -> a -> Type a -> UnifRes (TySubst a a)
extend phi x ty | ty == MFree x = return phi
                | occurs x ty   = throwError "occurs-check failed"
                | otherwise     = return $ deltaSub x ty . phi

unmoves :: Eq a => TySubst a a -> a -> Bool
unmoves phi x = applyTS phi x == MFree x

unifyEquation :: Ord a => TySubst a a -> UnifEquation a -> UnifRes (TySubst a a)
unifyEquation phi (MFree x, ty)
  | unmoves phi x = extend phi x (subType phi ty)
  | otherwise     = unifyEquation phi (applyTS phi x, subType phi ty)
unifyEquation phi eq@(MCtor _ _, MFree _) = unifyEquation phi (flipEq eq)
unifyEquation phi (MCtor name1 tys1, MCtor name2 tys2)
  | name1 == name2 = unifySet phi (zip tys1 tys2)
  | otherwise = throwError $ "cannot unify type ctors " ++ name1 ++ " and " ++ name2

unifySet :: Ord a => TySubst a a -> [UnifEquation a] -> UnifRes (TySubst a a)
unifySet phi = foldr unify' (return phi)
  where
    unify' eqn = (>>= flip unifyEquation eqn)

unify :: Ord a => [UnifEquation a] -> UnifRes (TySubst a a)
unify = unifySet id
