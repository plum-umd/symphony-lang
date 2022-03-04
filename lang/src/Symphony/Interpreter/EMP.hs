module Symphony.Interpreter.EMP where

import UVMHS
import AddToUVMHS

import Symphony.Interpreter.Types
import Symphony.Interpreter.Pretty ()

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types
import Foreign.Marshal.Utils
import Foreign.Marshal.Array

import qualified Prelude as HS
import qualified Data.Int as Int

type ChannelP     = Ptr ChannelStruct
type EMPProtocolP = Ptr EMPProtocolStruct
type EMPBoolP     = Ptr EMPBoolStruct
type EMPIntP      = Ptr EMPIntStruct

type Party = CSChar

toParty ∷ (HS.Integral a) ⇒ a → Party
toParty = HS.fromIntegral

withForeignPtrs ∷ (Functor t, FunctorM t) ⇒ t (ForeignPtr a) → (t (Ptr a) → IO b) → IO b
withForeignPtrs xs f = runCont (exchange $ map (cont ∘ withForeignPtr) xs) f

----------------------------
--- EMP Setup / Teardown ---
----------------------------

foreign import ccall unsafe "symphony/emp.h emp_semi_ctx_create"   emp_semi_ctx_create  ∷ Party → ChannelP → IO EMPProtocolP
foreign import ccall unsafe "symphony/emp.h &emp_semi_ctx_destroy" emp_semi_ctx_destroy ∷ FinalizerPtr EMPProtocolStruct

empSemiCtxCreate ∷ (Monad m, MonadIO m) ⇒ ℤ8 → Channel → m EMPProtocol
empSemiCtxCreate party chan = io $
  newForeignPtr emp_semi_ctx_destroy *$
  withForeignPtr chan $ \ chan_ptr →
  emp_semi_ctx_create (toParty party) chan_ptr

---------------------------------
--- Bit Sharing / Destruction ---
---------------------------------

foreign import ccall unsafe "symphony/emp.h emp_semi_bit_send_share" emp_semi_bit_send_share ∷ CBool → Ptr ChannelP → IO ()
foreign import ccall unsafe "symphony/emp.h emp_semi_bit_recv_share" emp_semi_bit_recv_share ∷ EMPProtocolP → ChannelP → IO EMPBoolP
foreign import ccall unsafe "symphony/emp.h emp_semi_bit_share"      emp_semi_bit_share      ∷ EMPProtocolP → Party → CBool → IO EMPBoolP
foreign import ccall unsafe "symphony/emp.h &emp_semi_bit_destroy"   emp_semi_bit_destroy    ∷ FinalizerPtr EMPBoolStruct

empSemiBitSendShare ∷ (Monad m, MonadIO m) ⇒ 𝔹 → 𝐿 Channel → m ()
empSemiBitSendShare b chans = io $
  withForeignPtrs chans $ \ chan_ptrs →
  withArray (tohs chan_ptrs) $ \ chans_ptr →
  emp_semi_bit_send_share (fromBool b) chans_ptr

empSemiBitRecvShare ∷ (Monad m, MonadIO m) ⇒ EMPProtocol → Channel → m EMPBool
empSemiBitRecvShare π chan = io $
  withForeignPtr π $ \ π_ptr →
  withForeignPtr chan $ \ chan_ptr →
  newForeignPtr emp_semi_bit_destroy *$ emp_semi_bit_recv_share π_ptr chan_ptr

empSemiBitShare ∷ (Monad m, MonadIO m) ⇒ EMPProtocol → ℤ8 → 𝔹 → m EMPBool
empSemiBitShare π party b = io $
  withForeignPtr π $ \ π_ptr →
  newForeignPtr emp_semi_bit_destroy *$ emp_semi_bit_share π_ptr (toParty party) (fromBool b)

---------------------
--- Bit Revealing ---
---------------------

foreign import ccall unsafe "symphony/emp.h emp_semi_bit_send_reveal" emp_semi_bit_send_reveal ∷ EMPProtocolP → EMPBoolP → ChannelP → IO ()
foreign import ccall unsafe "symphony/emp.h emp_semi_bit_recv_reveal" emp_semi_bit_recv_reveal ∷ Ptr ChannelP → IO CBool
foreign import ccall unsafe "symphony/emp.h emp_semi_bit_reveal"      emp_semi_bit_reveal      ∷ EMPProtocolP → Party → EMPBoolP → IO CBool

empSemiBitSendReveal ∷ (Monad m, MonadIO m) ⇒ EMPProtocol → EMPBool → Channel → m ()
empSemiBitSendReveal π sh chan = io $
  withForeignPtr π $ \ π_ptr →
  withForeignPtr sh $ \ sh_ptr →
  withForeignPtr chan $ \ chan_ptr →
  emp_semi_bit_send_reveal π_ptr sh_ptr chan_ptr

empSemiBitRecvReveal ∷ (Monad m, MonadIO m) ⇒ 𝐿 Channel → m 𝔹
empSemiBitRecvReveal chans = io $
  withForeignPtrs chans $ \ chan_ptrs →
  withArray (tohs chan_ptrs) $ \ chans_ptr →
  toBool ^$ emp_semi_bit_recv_reveal chans_ptr

empSemiBitReveal ∷ (Monad m, MonadIO m) ⇒ EMPProtocol → ℤ8 → EMPBool → m 𝔹
empSemiBitReveal π party sh = io $
  withForeignPtr π $ \ π_ptr →
  withForeignPtr sh $ \ sh_ptr →
  toBool ^$ emp_semi_bit_reveal π_ptr (toParty party) sh_ptr

----------------------
--- Bit Operations ---
----------------------

empUnary ∷ ForeignPtr a → (Ptr a → IO (Ptr b)) → FinalizerPtr b → IO (ForeignPtr b)
empUnary ev₁ f final = do
  withForeignPtr ev₁ $ \ evp₁ →
    newForeignPtr final *$ f evp₁

empBinary ∷ ForeignPtr a → ForeignPtr b → (Ptr a → Ptr b → IO (Ptr c)) → FinalizerPtr c → IO (ForeignPtr c)
empBinary ev₁ ev₂ f final = do
  withForeignPtr ev₁ $ \ evp₁ →
    withForeignPtr ev₂ $ \ evp₂ →
    newForeignPtr final *$ f evp₁ evp₂

empTernary ∷ ForeignPtr a → ForeignPtr b → ForeignPtr c → (Ptr a → Ptr b → Ptr c → IO (Ptr d)) → FinalizerPtr d → IO (ForeignPtr d)
empTernary ev₁ ev₂ ev₃ f final = do
  withForeignPtr ev₁ $ \ evp₁ →
    withForeignPtr ev₂ $ \ evp₂ →
    withForeignPtr ev₃ $ \ evp₃ →
    newForeignPtr final *$ f evp₁ evp₂ evp₃

foreign import ccall unsafe "symphony/emp.h emp_semi_bit_xor"  emp_semi_bit_xor  ∷ EMPProtocolP → EMPBoolP → EMPBoolP → IO EMPBoolP
foreign import ccall unsafe "symphony/emp.h emp_semi_bit_and"  emp_semi_bit_and  ∷ EMPProtocolP → EMPBoolP → EMPBoolP → IO EMPBoolP
foreign import ccall unsafe "symphony/emp.h emp_semi_bit_not"  emp_semi_bit_not  ∷ EMPProtocolP → EMPBoolP → IO EMPBoolP
foreign import ccall unsafe "symphony/emp.h emp_semi_bit_or"   emp_semi_bit_or   ∷ EMPProtocolP → EMPBoolP → EMPBoolP → IO EMPBoolP
foreign import ccall unsafe "symphony/emp.h emp_semi_bit_cond" emp_semi_bit_cond ∷ EMPProtocolP → EMPBoolP → EMPBoolP → EMPBoolP → IO EMPBoolP

empSemiBitXor ∷ (Monad m, MonadIO m) ⇒ EMPProtocol → EMPBool → EMPBool → m EMPBool
empSemiBitXor π sh₁ sh₂ = io $ withForeignPtr π $ \ π_ptr → empBinary sh₁ sh₂ (emp_semi_bit_xor π_ptr) emp_semi_bit_destroy

empSemiBitAnd ∷ (Monad m, MonadIO m) ⇒ EMPProtocol → EMPBool → EMPBool → m EMPBool
empSemiBitAnd π sh₁ sh₂ = io $ withForeignPtr π $ \ π_ptr → empBinary sh₁ sh₂ (emp_semi_bit_and π_ptr) emp_semi_bit_destroy

empSemiBitNot ∷ (Monad m, MonadIO m) ⇒ EMPProtocol → EMPBool → m EMPBool
empSemiBitNot π sh = io $ withForeignPtr π $ \ π_ptr → empUnary sh (emp_semi_bit_not π_ptr) emp_semi_bit_destroy

empSemiBitOr ∷ (Monad m, MonadIO m) ⇒ EMPProtocol → EMPBool → EMPBool → m EMPBool
empSemiBitOr π sh₁ sh₂ = io $ withForeignPtr π $ \ π_ptr → empBinary sh₁ sh₂ (emp_semi_bit_or π_ptr) emp_semi_bit_destroy

empSemiBitCond ∷ EMPProtocol → EMPBool → EMPBool → EMPBool → IO EMPBool
empSemiBitCond π sh₁ sh₂ sh₃ = io $ withForeignPtr π $ \ π_ptr → empTernary sh₁ sh₂ sh₃ (emp_semi_bit_cond π_ptr) emp_semi_bit_destroy

--- TODO: Integers
