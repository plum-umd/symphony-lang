module Symphony.Dynamic.Par.GMW.Types where

import Symphony.Prelude

import Foreign.ForeignPtr

type CGmw   = ()
newtype Gmw = Gmw { unGmw ∷ ForeignPtr CGmw }

type CGmwBool   = ()
newtype GmwBool = GmwBool { unGmwBool ∷ ForeignPtr CGmwBool }

type CGmwNat   = ()
newtype GmwNat = GmwNat { unGmwNat ∷ ForeignPtr CGmwNat }

type CGmwInt   = ()
newtype GmwInt = GmwInt { unGmwInt ∷ ForeignPtr CGmwInt }
