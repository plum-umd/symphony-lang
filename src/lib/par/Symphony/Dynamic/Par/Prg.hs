module Symphony.Dynamic.Par.Prg ( module Symphony.Dynamic.Par.Prg ) where

import Symphony.Prelude

import qualified Prelude as HS
import Foreign.ForeignPtr (newForeignPtr, withForeignPtr, FinalizerPtr)
import Foreign.Ptr (Ptr)
import Foreign.C.Types (CBool(..), CULong(..))
import Foreign.Marshal.Utils (toBool, fromBool)

import Symphony.Dynamic.Par.Prg.Types as Symphony.Dynamic.Par.Prg

foreign import ccall unsafe "&prg_drop" prg_drop ∷ FinalizerPtr CPrg

foreign import ccall unsafe "prg_new" prg_new ∷ IO (Ptr CPrg)

prgNew ∷ (Monad m, MonadIO m) ⇒ m Prg
prgNew = io $ Prg ^$ newForeignPtr prg_drop *$ prg_new

foreign import ccall unsafe "prg_from_seed" prg_from_seed ∷ CULong → CULong → IO (Ptr CPrg)

prgFromSeed ∷ (Monad m, MonadIO m) ⇒ ℕ → m Prg
prgFromSeed seed = io $ Prg ^$ newForeignPtr prg_drop *$ prg_from_seed cseed₁ cseed₂
  where cseed₁ = HS.fromIntegral $ HS.quot seed $ 2 ^ 64
        cseed₂ = HS.fromIntegral $ HS.rem seed $ 2 ^ 64

foreign import ccall unsafe "prg_rand_bool" prg_rand_bool ∷ Ptr CPrg → IO CBool

prgRandBool ∷ (Monad m, MonadIO m) ⇒ Prg → m 𝔹
prgRandBool prg = io $
  withForeignPtr cprg $ \ cprg_ptr →
  toBool ^$ prg_rand_bool cprg_ptr
  where cprg = unPrg prg
