{-# LANGUAGE PatternSynonyms, GADTs, DataKinds, KindSignatures #-}

module Types.DataDecl where

import Data.Set (empty)
import Types.Schemes
import Data.List.NonEmpty(NonEmpty(..))
import AST
import Types.Fin

data Kind :: Nat -> * where
  KStar :: Kind n
  KArrow :: Kind n -> Kind (Succ n) -> Kind (Succ n)

-- Helper patterns for up-to-rank-1 kinds
pattern KStar1 :: Kind (Succ Zero)
pattern KStar1 = KStar

pattern KArrow1 :: Kind (Succ Zero) -> Kind (Succ Zero)
pattern KArrow1 k = KArrow KStar k

-- data RawType = RTVar Name | RTCtor CtorName [RawType]
-- type RawDataDecl = (CtorName, Kind (Succ Zero), NonEmpty RawCtorDecl)
-- type RawCtorDecl = (CtorName, RawType)

type DataDecl a = (CtorName, Kind (Succ Zero), NonEmpty (CtorDecl a))
type CtorDecl a = (CtorName, TypeScheme a)

-- parseCtorDecl :: NonEmpty (CtorName, [Name]) -> TypeScheme Name
-- parseCtorDecl things = generalize empty ty
--   where
--     mapper (name, tyVars) = MCtor name (map MFree tyVars)
--     ty = foldr1 ArrowTy (fmap mapper things)
