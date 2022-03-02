module Symphony.Interpreter.EMP where

import UVMHS

import Symphony.Interpreter.Types
import Symphony.Interpreter.Pretty ()

import Foreign.Ptr
import Foreign.ForeignPtr

import qualified Prelude as HS
import qualified Data.Int as Int

----------------------------
--- EMP Setup / Teardown ---
----------------------------

foreign import ccall unsafe "backend-emp.h emp_semi_ctx_create"   emp_semi_ctx_create  ∷ CSChar → Ptr NetIOStruct → IO (Ptr EMPProtocolStruct)
foreign import ccall unsafe "backend-emp.h &emp_semi_ctx_destroy" emp_semi_ctx_destroy ∷ FinalizerPtr EMPProtocolStruct

empSemiCtxCreate ∷ ℤ8 → NetIO → IO EMPProtocol
empSemiCtxCreate party net = newForeignPtr emp_semi_ctx_destroy *$ withForeignPtr net $ \ netp → emp_semi_ctx_create party netp

foreign import ccall unsafe "backend-emp.h emp_semi_bit_send_share" emp_semi_bit_send_share ∷ CBool → Ptr CInt → CSize → IO ()
foreign import ccall unsafe "backend-emp.h emp_semi_bit_recv_share" emp_semi_bit_recv_share ∷ Ptr EMPProtocolStruct → CInt → IO (Ptr EMPBool)
foreign import ccall unsafe "backend-emp.h emp_semi_bit_share"      emp_semi_bit_share      ∷ Ptr EMPProtocolStruct → CSChar → CBool → IO (Ptr EMPBool)

empSemiBitSendShare ∷ 𝔹 → 𝐿 NetIO → IO ()
empSemiBitSendShare b ios = do
  sockets ← mapM netIOSocket ios
  withArrayLen sockets $ \ size fds → emp_semi_bit_send_share b fds size

foreign import ccall unsafe "backend-emp.h emp_semi_bit_create" bit_create ∷ (Ptr EMPProtocolStruct) → HS.Bool → HS.Int → IO (Ptr EMPBool)
foreign import ccall unsafe "backend-emp.h &emp_semi_bit_destroy" bit_destroy ∷ FinalizerPtr EMPBool
foreign import ccall unsafe "backend-emp.h emp_semi_integer_create" integer_create ∷ (Ptr EMPProtocolStruct) → HS.Int → Int.Int64 → HS.Int → IO (Ptr EMPInt)
foreign import ccall unsafe "backend-emp.h &emp_semi_integer_destroy" integer_destroy ∷ FinalizerPtr EMPInt

empShareBit ∷ EMPProtocol → HS.Int → 𝔹 → IO (ForeignPtr EMPBool)
empShareBit ep ρvFr b = withForeignPtr ep $ \ epp → newForeignPtr bit_destroy *$ bit_create epp b ρvFr

empShareInt ∷ EMPProtocol → HS.Int → HS.Int → ℤ → IO (ForeignPtr EMPInt)
empShareInt ep ρvFr prec z = withForeignPtr ep $ \ epp → newForeignPtr integer_destroy *$ integer_create epp prec (HS.fromIntegral z) ρvFr

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

foreign import ccall unsafe "backend-emp.h emp_semi_bit_not" bit_not ∷ Ptr EMPProtocolStruct → (Ptr EMPBool) → IO (Ptr EMPBool)
foreign import ccall unsafe "backend-emp.h emp_semi_bit_and" bit_and ∷ Ptr EMPProtocolStruct → (Ptr EMPBool) → (Ptr EMPBool) → IO (Ptr EMPBool)
foreign import ccall unsafe "backend-emp.h emp_semi_bit_cond" bit_cond ∷ Ptr EMPProtocolStruct → (Ptr EMPBool) → (Ptr EMPBool) → (Ptr EMPBool) → IO (Ptr EMPBool)

empBitNot ∷ EMPProtocol → ForeignPtr EMPBool → IO (ForeignPtr EMPBool)
empBitNot ep eb₁ = withForeignPtr ep $ \ epp → empUnary eb₁ (bit_not epp) bit_destroy

empBitAnd ∷ EMPProtocol → ForeignPtr EMPBool → ForeignPtr EMPBool → IO (ForeignPtr EMPBool)
empBitAnd ep eb₁ eb₂ = withForeignPtr ep $ \ epp → empBinary eb₁ eb₂ (bit_and epp) bit_destroy

empBitCond ∷ EMPProtocol → ForeignPtr EMPBool → ForeignPtr EMPBool → ForeignPtr EMPBool → IO (ForeignPtr EMPBool)
empBitCond ep eb₁ eb₂ eb₃ = withForeignPtr ep $ \ epp → empTernary eb₁ eb₂ eb₃ (bit_cond epp) bit_destroy

foreign import ccall unsafe "backend-emp.h emp_semi_integer_add" integer_add ∷ Ptr EMPProtocolStruct → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)
foreign import ccall unsafe "backend-emp.h emp_semi_integer_sub" integer_sub ∷ Ptr EMPProtocolStruct → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)
foreign import ccall unsafe "backend-emp.h emp_semi_integer_mult" integer_mult ∷ Ptr EMPProtocolStruct → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)
foreign import ccall unsafe "backend-emp.h emp_semi_integer_div" integer_div ∷ Ptr EMPProtocolStruct → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)
foreign import ccall unsafe "backend-emp.h emp_semi_integer_mod" integer_mod ∷ Ptr EMPProtocolStruct → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)
foreign import ccall unsafe "backend-emp.h emp_semi_integer_eq" integer_eq ∷ Ptr EMPProtocolStruct → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPBool)
foreign import ccall unsafe "backend-emp.h emp_semi_integer_lt" integer_lt ∷ Ptr EMPProtocolStruct → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPBool)
foreign import ccall unsafe "backend-emp.h emp_semi_integer_lte" integer_lte ∷ Ptr EMPProtocolStruct → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPBool)
foreign import ccall unsafe "backend-emp.h emp_semi_integer_gt" integer_gt ∷ Ptr EMPProtocolStruct → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPBool)
foreign import ccall unsafe "backend-emp.h emp_semi_integer_cond" integer_cond ∷ Ptr EMPProtocolStruct → (Ptr EMPBool) → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)

empIntegerAdd ∷ EMPProtocol → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerAdd ep ez₁ ez₂ = withForeignPtr ep $ \ epp → empBinary ez₁ ez₂ (integer_add epp) integer_destroy

empIntegerSub ∷ EMPProtocol → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerSub ep ez₁ ez₂ = withForeignPtr ep $ \ epp → empBinary ez₁ ez₂ (integer_sub epp) integer_destroy

empIntegerMult ∷ EMPProtocol → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerMult ep ez₁ ez₂ = withForeignPtr ep $ \ epp → empBinary ez₁ ez₂ (integer_mult epp) integer_destroy

empIntegerDiv ∷ EMPProtocol → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerDiv ep ez₁ ez₂ = withForeignPtr ep $ \ epp → empBinary ez₁ ez₂ (integer_div epp) integer_destroy

empIntegerMod ∷ EMPProtocol → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerMod ep ez₁ ez₂ = withForeignPtr ep $ \ epp → empBinary ez₁ ez₂ (integer_mod epp) integer_destroy

empIntegerEq ∷ EMPProtocol → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPBool)
empIntegerEq ep ez₁ ez₂ = withForeignPtr ep $ \ epp → empBinary ez₁ ez₂ (integer_eq epp) bit_destroy

empIntegerLt ∷ EMPProtocol → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPBool)
empIntegerLt ep ez₁ ez₂ = withForeignPtr ep $ \ epp → empBinary ez₁ ez₂ (integer_lt epp) bit_destroy

empIntegerLte ∷ EMPProtocol → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPBool)
empIntegerLte ep ez₁ ez₂ = withForeignPtr ep $ \ epp → empBinary ez₁ ez₂ (integer_lte epp) bit_destroy

empIntegerGt ∷ EMPProtocol → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPBool)
empIntegerGt ep ez₁ ez₂ = withForeignPtr ep $ \ epp → empBinary ez₁ ez₂ (integer_gt epp) bit_destroy

empIntegerCond ∷ EMPProtocol → ForeignPtr EMPBool → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerCond ep eb₁ ez₂ ez₃ = withForeignPtr ep $ \ epp → empTernary eb₁ ez₂ ez₃ (integer_cond epp) integer_destroy

foreign import ccall unsafe "backend-emp.h emp_semi_bit_reveal" bit_reveal ∷ Ptr EMPProtocolStruct → (Ptr EMPBool) → HS.Int → IO HS.Bool
foreign import ccall unsafe "backend-emp.h emp_semi_integer_reveal" integer_reveal ∷ Ptr EMPProtocolStruct → (Ptr EMPInt) → HS.Int → IO Int.Int64

empBitReveal ∷ EMPProtocol → HS.Int → ForeignPtr EMPBool → IO 𝔹
empBitReveal ep ρvTo eb = withForeignPtr ep $ \ epp → withForeignPtr eb $ \ ebp → bit_reveal epp ebp ρvTo

empIntegerReveal ∷ EMPProtocol → HS.Int → ForeignPtr EMPInt → IO Int.Int64
empIntegerReveal ep ρvTo ez = withForeignPtr ep $ \ epp → withForeignPtr ez $ \ ezp → integer_reveal epp ezp ρvTo
