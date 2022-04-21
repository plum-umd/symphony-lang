module Symphony.Dynamic.Par.Prg ( module Symphony.Dynamic.Par.Prg ) where

import Symphony.Prelude

import qualified Prelude as HS
import Foreign.ForeignPtr (newForeignPtr, withForeignPtr, FinalizerPtr)
import Foreign.Ptr (Ptr)
import Foreign.C.Types (CBool(..))
import Foreign.Marshal.Utils (toBool, fromBool)

import Symphony.Dynamic.Par.Prg.Types as Symphony.Dynamic.Par.Prg

foreign import ccall unsafe "prg_rand_bool" prg_rand_bool ∷ Ptr CPrg → IO CBool

prgRandBool ∷ (Monad m, MonadIO m) ⇒ Prg → m 𝔹
prgRandBool prg = io $
  withForeignPtr cprg $ \ cprg_ptr →
  toBool ^$ prg_rand_bool cprg_ptr
  where cprg = unPrg prg
