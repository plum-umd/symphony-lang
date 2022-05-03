module Symphony.Dynamic.Par.Prg ( module Symphony.Dynamic.Par.Prg ) where

import Symphony.Prelude

import qualified Prelude as HS
import Foreign.ForeignPtr (newForeignPtr, withForeignPtr, FinalizerPtr)
import Foreign.Ptr (Ptr)
import Foreign.C.Types (CBool(..), CULong(..), CUInt(..))
import Foreign.Marshal.Utils (toBool, fromBool)

import Symphony.Dynamic.Par.Prg.Types as Symphony.Dynamic.Par.Prg

foreign import ccall unsafe "&prg_drop" prg_drop ∷ FinalizerPtr CPrg

foreign import ccall unsafe "prg_new" prg_new ∷ IO (Ptr CPrg)

prgNew ∷ (Monad m, MonadIO m) ⇒ m Prg
prgNew = io $ Prg ^$ newForeignPtr prg_drop *$ prg_new

foreign import ccall unsafe "prg_from_seed" prg_from_seed ∷ CULong → CULong → IO (Ptr CPrg)

prgFromSeed ∷ (Monad m, MonadIO m) ⇒ (ℕ64 ∧ ℕ64) → m Prg
prgFromSeed (seed₁ :* seed₂) = io $ Prg ^$ newForeignPtr prg_drop *$ prg_from_seed cseed₁ cseed₂
  where cseed₁ = HS.fromIntegral seed₁
        cseed₂ = HS.fromIntegral seed₂

foreign import ccall unsafe "prg_rand_bool" prg_rand_bool ∷ Ptr CPrg → IO CBool

prgRandBool ∷ (Monad m, MonadIO m) ⇒ Prg → m 𝔹
prgRandBool prg = io $
  withForeignPtr cprg $ \ cprg_ptr →
  toBool ^$ prg_rand_bool cprg_ptr
  where cprg = unPrg prg

foreign import ccall unsafe "prg_rand_u32" prg_rand_u32 ∷ Ptr CPrg → IO CUInt

prgRandNat32 ∷ (Monad m, MonadIO m) ⇒ Prg → m ℕ32
prgRandNat32 prg = io $
  withForeignPtr cprg $ \ cprg_ptr →
  HS.fromIntegral ^$ prg_rand_u32 cprg_ptr
  where cprg = unPrg prg

foreign import ccall unsafe "prg_rand_u64" prg_rand_u64 ∷ Ptr CPrg → IO CULong

prgRandSeed ∷ (Monad m, MonadIO m) ⇒ Prg → m (ℕ64 ∧ ℕ64)
prgRandSeed prg = io $
  withForeignPtr (unPrg prg) $ \ cprg_ptr → do
  a ← HS.fromIntegral ^$ prg_rand_u64 cprg_ptr
  b ← HS.fromIntegral ^$ prg_rand_u64 cprg_ptr
  return $ a :* b
