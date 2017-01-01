{-# LANGUAGE StandaloneDeriving, DataKinds, GADTs, KindSignatures #-}

module Types.Fin where

data Nat = Zero | Succ Nat

data Fin :: Nat -> * where
  FZero :: Fin (Succ n)
  FSucc :: Fin n -> Fin (Succ n)

instance Show (Fin n) where
  show = show . toInt

deriving instance Eq (Fin n)
deriving instance Ord (Fin n)

data NNat :: Nat -> * where
  NZero :: NNat Zero
  NSucc :: NNat n -> NNat (Succ n)

toInt :: Fin n -> Int
toInt FZero = 0
toInt (FSucc fin) = 1 + toInt fin

raiseFin :: Fin n -> Fin (Succ n)
raiseFin FZero = FZero
raiseFin (FSucc fin) = FSucc (raiseFin fin)

maxOfFin :: NNat n -> Fin (Succ n)
maxOfFin NZero = FZero
maxOfFin (NSucc nn) = FSucc (maxOfFin nn)

thick :: NNat n -> Fin (Succ n) -> Fin (Succ n) -> Maybe (Fin n)
thick NZero FZero FZero = Nothing
thick NZero FZero (FSucc f2) = Just f2
thick (NSucc _) FZero FZero = Nothing
thick (NSucc _) FZero (FSucc f2) = Just f2
thick (NSucc _) (FSucc _) FZero = Just FZero
thick (NSucc n) (FSucc f1) (FSucc f2) = fmap FSucc (thick n f1 f2)
