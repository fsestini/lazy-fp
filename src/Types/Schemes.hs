{-# LANGUAGE GADTs, DataKinds, KindSignatures, PatternSynonyms #-}

module Types.Schemes(
  Monotype(..),
  Type,
  Scheme(..),
  TypeScheme,
  fullyInst,
  generalize,
  TySubst(..),
  subType,
  deltaSub,
  occurs,
  schemeSub,
  schemeFreeVars,
  (-->),
  pattern IntTy,
  pattern BoolTy,
  pattern ArrowTy,
  schemeArity
) where

import Prelude hiding ((.))
import PickFresh
import Data.Maybe (fromMaybe)
import Control.Monad
import qualified Data.Set as S
import qualified Data.Map as M
import Stream hiding (map)
import Types.Fin
import AST (CtorName)
import Control.Category (Category (..))

infixr 5 -->
(-->) :: Monotype n a -> Monotype n a -> Monotype n a
t1 --> t2 = MCtor "arrow" [t1, t2]

pattern IntTy = MCtor "Int" []
pattern BoolTy = MCtor "Bool" []
pattern ArrowTy t1 t2 = MCtor "arrow" [t1, t2]

data Monotype :: Nat -> * -> * where
  MFree :: a -> Monotype n a
  MBound :: Fin n -> Monotype n a
  MCtor :: CtorName -> [Monotype n a] -> Monotype n a
  deriving (Eq, Ord)

instance Show a => Show (Monotype n a) where
  show (ArrowTy t1 t2) = show t1 ++ " -> " ++ show t2
  show (MFree x) = show x
  show (MBound fin) = show . toInt $ fin
  show (MCtor name tys) = name ++ join (map show tys)

instance Functor (Monotype n) where
  fmap f (MFree x) = MFree (f x)
  fmap f (MCtor x1 x2) = MCtor x1 $ fmap (fmap f) x2
  fmap _ (MBound x) = MBound x

instance Applicative (Monotype n) where
  pure = MFree
  (<*>) = ap

instance Monad (Monotype n) where
  return = pure
  (MFree x) >>= f = f x
  (MBound x) >>= _ = MBound x
  (MCtor name tys) >>= f = MCtor name (fmap (f =<<) tys)

raiseMono :: Monotype Zero a -> Monotype n a
raiseMono (MFree x) = MFree x
raiseMono (MCtor name ms) = MCtor name $ map raiseMono ms

monoFreeVars :: Ord a => Monotype n a -> S.Set a
monoFreeVars (MFree x) = S.singleton x
monoFreeVars (MBound _) = S.empty
monoFreeVars (MCtor _ ms) = foldr (S.union . monoFreeVars) S.empty ms

data Scheme :: Nat -> * -> * where
  SMono :: Monotype n a -> Scheme n a
  SForall :: Scheme ('Succ n) a -> Scheme n a

schemeFreeVars :: Ord a => Scheme n a -> S.Set a
schemeFreeVars (SMono m) = monoFreeVars m
schemeFreeVars (SForall sc) = schemeFreeVars sc

monoArity :: Monotype n a -> Int
monoArity (ArrowTy t1 t2) = 1 + monoArity t2
monoArity (MFree m) = 0
monoArity (MBound m) = 0
monoArity (MCtor _ _) = 0

schemeArity :: Scheme n a -> Int
schemeArity (SMono mono) = monoArity mono
schemeArity (SForall sc) = schemeArity sc

type TypeScheme a = Scheme Zero a
type Type a = Monotype 'Zero a

thickMono :: NNat n -> a -> Fin (Succ n) -> Monotype (Succ n) a -> Monotype n a
thickMono _ _ _ (MFree y) = MFree y
thickMono n x fin (MBound y) = case thick n fin y of
  Just x -> MBound x
  Nothing -> MFree x
thickMono n x fin (MCtor name ms) = MCtor name (map (thickMono n x fin) ms)

thickScheme :: NNat n -> a -> Fin (Succ n) -> Scheme (Succ n) a -> Scheme n a
thickScheme n x fin (SMono m) = SMono (thickMono n x fin m)
thickScheme n x fin (SForall scheme)
  = SForall (thickScheme (NSucc n) x (FSucc fin) scheme)

fullyInst :: TypeScheme a -> Stream a -> (Type a, Stream a)
fullyInst (SMono m) str = (m, str)
fullyInst (SForall sc) (Cons x xs) = fullyInst (thickScheme NZero x FZero sc) xs

bindInMono :: Eq a => NNat n -> a -> Monotype n a -> Monotype (Succ n) a
bindInMono n x (MFree y) = if x == y then MBound (maxOfFin n) else MFree y
bindInMono n x (MBound y) = MBound (raiseFin y)
bindInMono n x (MCtor name tys) = MCtor name (map (bindInMono n x) tys)

bindInScheme :: Eq a => NNat n -> a -> Scheme n a -> Scheme (Succ n) a
bindInScheme n x (SMono mono) = SMono (bindInMono n x mono)
bindInScheme n x (SForall sc) = SForall (bindInScheme (NSucc n) x sc)

abstract :: Eq a => a -> TypeScheme a -> TypeScheme a
abstract x = SForall . bindInScheme NZero x

genericVars :: Ord a => S.Set a -> Monotype n a -> S.Set a
genericVars ctxt = S.filter (\x -> not (S.member x ctxt)) . monoFreeVars

generalize :: Ord a => S.Set a -> Type a -> TypeScheme a
generalize ctxt mono = S.foldr abstract (SMono mono) (genericVars ctxt mono)

newtype TySubst a b = TySubst { applyTS :: a -> Type b }

instance Category TySubst where
  id = TySubst return
  TySubst f . TySubst g = TySubst (f <=< g)

subType :: TySubst a b -> Monotype n a -> Monotype n b
subType f = ((raiseMono . applyTS f) =<<)

deltaSub :: Eq a => a -> Type a -> TySubst a a
deltaSub x ty = TySubst $ \y ->
  if x == y then ty else return y

occurs :: Ord a => a -> Type a -> Bool
occurs x ty = S.member x $ monoFreeVars ty

schemeSub :: TySubst a b -> Scheme n a -> Scheme n b
schemeSub phi (SMono m) = SMono . subType phi $ m
schemeSub phi (SForall sc) = SForall (schemeSub phi sc)

--------------------------------------------------------------------------------
-- Show instance for type schemes

instance Show a => Show (Scheme n a) where
  show = showAux M.empty

showAux :: Show a => M.Map Int String -> Scheme n a -> String
showAux m (SMono mono) = showAuxMono m mono
showAux m (SForall sc) = "∀ " ++ newSym ++ " . " ++
  showAux (M.insert 0 newSym (M.mapKeys (+1) m)) sc
  where
    newSym = show (pickNTh (M.size m) :: Greek)

showAuxMono :: Show a => M.Map Int String -> Monotype n a -> String
showAuxMono m (MFree free) = show free
showAuxMono m (MBound b) =
  fromMaybe (error "show scheme") (M.lookup (toInt b) m)
showAuxMono m (ArrowTy t1 t2) =
  "(" ++ showAuxMono m t1 ++ ") -> " ++ showAuxMono m t2
showAuxMono m (MCtor name tys) =
  name ++ join (map (\t -> "(" ++ showAuxMono m t ++ ")") tys)

newtype Greek = G { unG :: Int }

instance Show Greek where
  show (G i) = fromMod (i `mod` 4) ++
               let d = i `div` 4 in if d == 0 then "" else show (d - 1)
    where
      fromMod 0 = "α"
      fromMod 1 = "β"
      fromMod 2 = "γ"
      fromMod 3 = "δ"

instance PickFresh Greek where
  pickFresh [] = G 0
  pickFresh used = G $ maximum (map unG used) + 1
