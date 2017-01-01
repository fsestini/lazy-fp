{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module PrettyClass where

import Text.PrettyPrint

-- <super-hack>

class Pretty a where
  pPrint :: a -> Doc

instance Pretty String where
  pPrint = text

-- </super-hack>
