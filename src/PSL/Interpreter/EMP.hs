module PSL.Interpreter.EMP where

import UVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.String

import qualified Prelude as HS
import qualified Data.Int as Int
import qualified Data.Text as Text

-------------
--- NetIO ---
-------------

foreign import ccall "empc.h netio_create" netio_create ∷ CString → HS.Int → IO NetIO
foreign import ccall "empc.h netio_destroy" netio_destroy ∷ NetIO → IO ()

netIOCreate ∷ 𝑂 𝕊 → HS.Int → IO NetIO
netIOCreate oaddr port = case oaddr of
  None      → netio_create nullPtr port
  Some addr → withCString (Text.unpack addr) $ \ csaddr → netio_create csaddr port

netIODestroy ∷ NetIO → IO ()
netIODestroy = netio_destroy

-----------------
--- EMP Setup ---
-----------------

foreign import ccall "empc.h setup_semi_honest_c" setup_semi_honest_c ∷ NetIO → HS.Int → IO SemiHonest
foreign import ccall "empc.h finalize_semi_honest_c" finalize_semi_honest_c ∷ SemiHonest → IO ()

{-
teardownEMP ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ PrinVal → m ()
teardownEMP ρv = do
  sessions ← getL iStateSessionsYaoL
  sess ← fromSomeCxt $ sessions ⋕? ρv
  io $ finalize_semi_honest_c $ semiHonestES sess
  io $ netio_destroy $ channelES sess
  putL iStateSessionsYaoL (delete ρv sessions)
-}

empType ∷ EMPVal → BaseType
empType = \case
  BoolEV   _ → 𝔹T
  NatEV pr _ → ℕT pr
  IntEV pr _ → ℤT pr
  FltEV pr _ → 𝔽T pr

foreign import ccall "empc.h bit_create" bit_create ∷ SemiHonest → HS.Bool → HS.Int → IO (Ptr EMPBool)
foreign import ccall "empc.h &bit_destroy" bit_destroy ∷ FinalizerPtr EMPBool
foreign import ccall "empc.h integer_create" integer_create ∷ SemiHonest → HS.Int → Int.Int64 → HS.Int → IO (Ptr EMPInt)
foreign import ccall "empc.h &integer_destroy" integer_destroy ∷ FinalizerPtr EMPInt

empShareBit ∷ SemiHonest → HS.Int → 𝔹 → IO (ForeignPtr EMPBool)
empShareBit sh ρvFr b = newForeignPtr bit_destroy *$ bit_create sh b ρvFr

empShareInt ∷ SemiHonest → HS.Int → HS.Int → ℤ → IO (ForeignPtr EMPInt)
empShareInt sh ρvFr prec z = newForeignPtr integer_destroy *$ integer_create sh prec (HS.fromIntegral z) ρvFr

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

foreign import ccall "empc.h bit_not" bit_not ∷ SemiHonest → (Ptr EMPBool) → IO (Ptr EMPBool)
foreign import ccall "empc.h bit_and" bit_and ∷ SemiHonest → (Ptr EMPBool) → (Ptr EMPBool) → IO (Ptr EMPBool)
foreign import ccall "empc.h bit_cond" bit_cond ∷ SemiHonest → (Ptr EMPBool) → (Ptr EMPBool) → (Ptr EMPBool) → IO (Ptr EMPBool)

empBitNot ∷ SemiHonest → ForeignPtr EMPBool → IO (ForeignPtr EMPBool)
empBitNot sh eb₁ = empUnary eb₁ (bit_not sh) bit_destroy

empBitAnd ∷ SemiHonest → ForeignPtr EMPBool → ForeignPtr EMPBool → IO (ForeignPtr EMPBool)
empBitAnd sh eb₁ eb₂ = empBinary eb₁ eb₂ (bit_and sh) bit_destroy

empBitCond ∷ SemiHonest → ForeignPtr EMPBool → ForeignPtr EMPBool → ForeignPtr EMPBool → IO (ForeignPtr EMPBool)
empBitCond sh eb₁ eb₂ eb₃ = empTernary eb₁ eb₂ eb₃ (bit_cond sh) bit_destroy

foreign import ccall "empc.h integer_add" integer_add ∷ SemiHonest → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)
foreign import ccall "empc.h integer_sub" integer_sub ∷ SemiHonest → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)
foreign import ccall "empc.h integer_mult" integer_mult ∷ SemiHonest → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)
foreign import ccall "empc.h integer_div" integer_div ∷ SemiHonest → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)
foreign import ccall "empc.h integer_mod" integer_mod ∷ SemiHonest → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)
foreign import ccall "empc.h integer_eq" integer_eq ∷ SemiHonest → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPBool)
foreign import ccall "empc.h integer_lt" integer_lt ∷ SemiHonest → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPBool)
foreign import ccall "empc.h integer_gt" integer_gt ∷ SemiHonest → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPBool)
foreign import ccall "empc.h integer_cond" integer_cond ∷ SemiHonest → (Ptr EMPBool) → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)

empIntegerAdd ∷ SemiHonest → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerAdd sh ez₁ ez₂ = empBinary ez₁ ez₂ (integer_add sh) integer_destroy

empIntegerSub ∷ SemiHonest → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerSub sh ez₁ ez₂ = empBinary ez₁ ez₂ (integer_sub sh) integer_destroy

empIntegerMult ∷ SemiHonest → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerMult sh ez₁ ez₂ = empBinary ez₁ ez₂ (integer_mult sh) integer_destroy

empIntegerDiv ∷ SemiHonest → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerDiv sh ez₁ ez₂ = empBinary ez₁ ez₂ (integer_div sh) integer_destroy

empIntegerMod ∷ SemiHonest → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerMod sh ez₁ ez₂ = empBinary ez₁ ez₂ (integer_mod sh) integer_destroy

empIntegerEq ∷ SemiHonest → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPBool)
empIntegerEq sh ez₁ ez₂ = empBinary ez₁ ez₂ (integer_eq sh) bit_destroy

empIntegerLt ∷ SemiHonest → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPBool)
empIntegerLt sh ez₁ ez₂ = empBinary ez₁ ez₂ (integer_lt sh) bit_destroy

empIntegerGt ∷ SemiHonest → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPBool)
empIntegerGt sh ez₁ ez₂ = empBinary ez₁ ez₂ (integer_gt sh) bit_destroy

empIntegerCond ∷ SemiHonest → ForeignPtr EMPBool → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerCond sh eb₁ ez₂ ez₃ = empTernary eb₁ ez₂ ez₃ (integer_cond sh) integer_destroy

foreign import ccall "empc.h bit_reveal" bit_reveal ∷ SemiHonest → (Ptr EMPBool) → HS.Int → IO HS.Bool
foreign import ccall "empc.h integer_reveal" integer_reveal ∷ SemiHonest → (Ptr EMPInt) → HS.Int → IO Int.Int64

empBitReveal ∷ SemiHonest → HS.Int → ForeignPtr EMPBool → IO 𝔹
empBitReveal sh ρvTo eb = withForeignPtr eb $ \ ebp → bit_reveal sh ebp ρvTo

empIntegerReveal ∷ SemiHonest → HS.Int → ForeignPtr EMPInt → IO Int.Int64
empIntegerReveal sh ρvTo ez = withForeignPtr ez $ \ ezp → integer_reveal sh ezp ρvTo
