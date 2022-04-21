module Symphony.Dynamic.Par.Prg.Types where

import Symphony.Prelude

import Foreign.ForeignPtr

type CPrg = ()
newtype Prg = Prg { unPrg ∷ ForeignPtr CPrg } deriving (Eq, Ord, Show)
