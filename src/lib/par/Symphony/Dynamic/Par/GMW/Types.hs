module Symphony.Dynamic.Par.GMW.Types where

import Symphony.Prelude

import Foreign.ForeignPtr

type CGmw = ()
newtype Gmw = Gmw { unGmw ∷ ForeignPtr CGmw }

type CGmwBool = ()
newtype GmwBool = GmwBool { unGmwBool ∷ ForeignPtr CGmwBool }

instance Pretty GmwBool where
  pretty _ = ppCon "𝔹"

type CGmwNat64 = ()
newtype GmwNat64 = GmwNat64 { unGmwNat64 ∷ ForeignPtr CGmwNat64 }

type CGmwInt64 = ()
newtype GmwInt64 = GmwInt64 { unGmwInt64 ∷ ForeignPtr CGmwInt64 }
