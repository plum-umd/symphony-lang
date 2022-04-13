module Symphony.Dynamic.Seq.MPSPDZ where

import UVMHS

import Symphony.Dynamic.Seq.Types

import Foreign.Ptr
import Foreign.ForeignPtr

import qualified Prelude as HS
import qualified Data.Int as Int

--------------------------------
--- MP-SPDZ Semi 2^K, K = 64 ---
--------------------------------

------------------------
--- Setup / Teardown ---
------------------------

foreign import ccall unsafe "symphony_backends.h mpspdz_create" mpspdz_create ∷ HS.Int → HS.Int → IO (Ptr MPSPDZProtocolStruct)
foreign import ccall unsafe "symphony_backends.h &mpspdz_destroy" mpspdz_destroy ∷ FinalizerPtr MPSPDZProtocolStruct

mpspdzCreate ∷ HS.Int → HS.Int → IO MPSPDZProtocol
mpspdzCreate party num_parties = newForeignPtr mpspdz_destroy *$ mpspdz_create party num_parties

-------------
--- Share ---
-------------

foreign import ccall unsafe "symphony_backends.h mpspdz_integer_share" mpspdz_integer_share ∷ (Ptr MPSPDZProtocolStruct) → HS.Int → Int.Int64 → IO (Ptr MPSPDZInt)
foreign import ccall unsafe "symphony_backends.h &mpspdz_integer_destroy" mpspdz_integer_destroy ∷ FinalizerPtr MPSPDZInt

mpspdzIntegerShare ∷ MPSPDZProtocol → HS.Int → Int.Int64 → IO (ForeignPtr MPSPDZInt)
mpspdzIntegerShare mp ρvFr z = withForeignPtr mp $ \ mpp → newForeignPtr mpspdz_integer_destroy *$ mpspdz_integer_share mpp ρvFr z

-------------
--- Embed ---
-------------

foreign import ccall unsafe "symphony_backends.h mpspdz_integer_embed" mpspdz_integer_embed ∷ Ptr MPSPDZProtocolStruct → Int.Int64 → IO (Ptr MPSPDZInt)

mpspdzIntegerEmbed ∷ MPSPDZProtocol → Int.Int64 → IO (ForeignPtr MPSPDZInt)
mpspdzIntegerEmbed mp z = withForeignPtr mp $ \ mpp → newForeignPtr mpspdz_integer_destroy *$ mpspdz_integer_embed mpp z

------------------
--- Operations ---
------------------

foreign import ccall unsafe "symphony_backends.h mpspdz_integer_mult" mpspdz_integer_mult ∷ Ptr MPSPDZProtocolStruct → Ptr MPSPDZInt → Ptr MPSPDZInt → IO (Ptr MPSPDZInt)

mpspdzIntegerMult ∷ MPSPDZProtocol → ForeignPtr MPSPDZInt → ForeignPtr MPSPDZInt → IO (ForeignPtr MPSPDZInt)
mpspdzIntegerMult mp mpz₁ mpz₂ =
  withForeignPtr mp   $ \ mpp   →
  withForeignPtr mpz₁ $ \ mpzp₁ →
  withForeignPtr mpz₂ $ \ mpzp₂ →
  newForeignPtr mpspdz_integer_destroy *$ mpspdz_integer_mult mpp mpzp₁ mpzp₂

--------------
--- Reveal ---
--------------

foreign import ccall unsafe "symphony_backends.h mpspdz_integer_reveal" mpspdz_integer_reveal ∷ Ptr MPSPDZProtocolStruct → HS.Int → (Ptr MPSPDZInt) → IO Int.Int64

mpspdzIntegerReveal ∷ MPSPDZProtocol → HS.Int → ForeignPtr MPSPDZInt → IO Int.Int64
mpspdzIntegerReveal mp party mpz =
  withForeignPtr mp  $ \ mpp  →
  withForeignPtr mpz $ \ mpzp →
  mpspdz_integer_reveal mpp party mpzp
