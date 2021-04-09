module PSL.Interpreter.EMP where

import UVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Lens
import PSL.Interpreter.Error

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.String

import qualified Prelude as HS
import qualified Data.Int as Int
import qualified Data.Text as Text

--------------------------
--- Serializing to EMP ---
--------------------------

serializeMode ∷ (Monad m, MonadReader ICxt m, MonadError IError m) ⇒ Mode → m HS.Int
serializeMode = \case
  TopM     → return $ HS.fromIntegral 0
  SecM ρvs → case list ρvs of
    (SinglePV "A") :& Nil                   → return $ HS.fromIntegral 1
    (SinglePV "B") :& Nil                   → return $ HS.fromIntegral 2
    (SinglePV "A") :& (SinglePV "B") :& Nil → return $ HS.fromIntegral 0
    m                                       → throwIErrorCxt TypeIError "[Yao] serializeMode: only parties A and B allowed" $ frhs [ ("m", pretty m) ]

serializePrec ∷ (Monad m, MonadReader ICxt m, MonadError IError m) ⇒ IPrecision → m HS.Int
serializePrec = \case
  FixedIPr 64 0 → return $ HS.fromIntegral 64
  pr → throwIErrorCxt NotImplementedIError "[Yao] serializePrec: precision pr not supported" $ frhs [ ("pr", pretty pr) ]

-------------
--- NetIO ---
-------------

data NetIOStruct = NetIOStruct
type NetIO = Ptr NetIOStruct -- Cannot be ForeignPtr because EMP holds an internal reference

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

foreign import ccall "empc.h setup_semi_honest_c" setup_semi_honest_c ∷ NetIO → HS.Int → IO ()

initializeEMP ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ m ()
initializeEMP = do
  lm    ← askL iCxtLocalModeL
  party ← serializeMode lm
  let addr = if isAlice party then None else Some localhost
  net ← io $ netIOCreate addr port
  io $ setup_semi_honest_c net party
  where localhost = "127.0.0.1"
        port      = HS.fromIntegral 12345
        isAlice p = p ≡ HS.fromIntegral 1

initializeIfNecessary ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ m ()
initializeIfNecessary = do
  initialized ← getL iStateYaoInitL
  if initialized
    then return ()
    else do
    initializeEMP
    putL iStateYaoInitL True

empType ∷ EMPVal → BaseType
empType = \case
  BoolEV _   → 𝔹T
  NatEV pr _ → ℕT pr
  IntEV pr _ → ℤT pr
  FltEV pr _ → 𝔽T pr

foreign import ccall "empc.h bit_create" bit_create ∷ HS.Bool → HS.Int → IO (Ptr EMPBool)
foreign import ccall "empc.h &bit_destroy" bit_destroy ∷ FinalizerPtr EMPBool
foreign import ccall "empc.h integer_create" integer_create ∷ HS.Int → Int.Int64 → HS.Int → IO (Ptr EMPInt)
foreign import ccall "empc.h &integer_destroy" integer_destroy ∷ FinalizerPtr EMPInt

empShare ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ 𝑃 PrinVal → 𝑃 PrinVal → BaseVal → m EMPVal
empShare _ρvsComputing ρvsSharing bv = do
  initializeIfNecessary
  party ← serializeMode (SecM ρvsSharing)
  case bv of
    BoolBV b   → map BoolEV $ io $ newForeignPtr bit_destroy *$ bit_create b party
    NatBV pr n → do
      prec ← serializePrec pr
      map (NatEV pr) $ io $ newForeignPtr integer_destroy *$ integer_create prec (HS.fromIntegral n) party
    IntBV pr z → do
      prec ← serializePrec pr
      map (IntEV pr) $ io $ newForeignPtr integer_destroy *$ integer_create prec (HS.fromIntegral z) party
    FltBV pr f → throwIErrorCxt NotImplementedIError "[Yao] empShare: 𝔻 (Float) not implemented" empty𝐿

foreign import ccall "empc.h bit_not" bit_not ∷ (Ptr EMPBool) → IO (Ptr EMPBool)
foreign import ccall "empc.h bit_and" bit_and ∷ (Ptr EMPBool) → (Ptr EMPBool) → IO (Ptr EMPBool)
foreign import ccall "empc.h bit_cond" bit_cond ∷ (Ptr EMPBool) → (Ptr EMPBool) → (Ptr EMPBool) → IO (Ptr EMPBool)

empBitNot ∷ ForeignPtr EMPBool → IO (ForeignPtr EMPBool)
empBitNot eb₁ = do
  withForeignPtr eb₁ $ \ ebp₁ →
    newForeignPtr bit_destroy *$ bit_not ebp₁

empBitAnd ∷ ForeignPtr EMPBool → ForeignPtr EMPBool → IO (ForeignPtr EMPBool)
empBitAnd eb₁ eb₂ = do
  withForeignPtr eb₁ $ \ ebp₁ →
    withForeignPtr eb₂ $ \ ebp₂ →
    newForeignPtr bit_destroy *$ bit_and ebp₁ ebp₂

empBitCond ∷ ForeignPtr EMPBool → ForeignPtr EMPBool → ForeignPtr EMPBool → IO (ForeignPtr EMPBool)
empBitCond eb₁ eb₂ eb₃ = do
  withForeignPtr eb₁ $ \ ebp₁ →
    withForeignPtr eb₂ $ \ ebp₂ →
    withForeignPtr eb₃ $ \ ebp₃ →
    newForeignPtr bit_destroy *$ bit_cond ebp₁ ebp₂ ebp₃

foreign import ccall "empc.h integer_add" integer_add ∷ (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)
foreign import ccall "empc.h integer_sub" integer_sub ∷ (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)
foreign import ccall "empc.h integer_mult" integer_mult ∷ (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)
foreign import ccall "empc.h integer_div" integer_div ∷ (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)
foreign import ccall "empc.h integer_eq" integer_eq ∷ (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPBool)
foreign import ccall "empc.h integer_lt" integer_lt ∷ (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPBool)
foreign import ccall "empc.h integer_cond" integer_cond ∷ (Ptr EMPBool) → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)

empIntegerAdd ∷ ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerAdd ez₁ ez₂ = do
  withForeignPtr ez₁ $ \ ezp₁ →
    withForeignPtr ez₂ $ \ ezp₂ →
    newForeignPtr integer_destroy *$ integer_add ezp₁ ezp₂

empIntegerSub ∷ ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerSub ez₁ ez₂ = do
  withForeignPtr ez₁ $ \ ezp₁ →
    withForeignPtr ez₂ $ \ ezp₂ →
    newForeignPtr integer_destroy *$ integer_sub ezp₁ ezp₂

empIntegerMult ∷ ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerMult ez₁ ez₂ = do
  withForeignPtr ez₁ $ \ ezp₁ →
    withForeignPtr ez₂ $ \ ezp₂ →
    newForeignPtr integer_destroy *$ integer_mult ezp₁ ezp₂

empIntegerDiv ∷ ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerDiv ez₁ ez₂ = do
  withForeignPtr ez₁ $ \ ezp₁ →
    withForeignPtr ez₂ $ \ ezp₂ →
    newForeignPtr integer_destroy *$ integer_div ezp₁ ezp₂

empIntegerEq ∷ ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPBool)
empIntegerEq ez₁ ez₂ = do
  withForeignPtr ez₁ $ \ ezp₁ →
    withForeignPtr ez₂ $ \ ezp₂ →
    newForeignPtr bit_destroy *$ integer_eq ezp₁ ezp₂

empIntegerLt ∷ ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPBool)
empIntegerLt ez₁ ez₂ = do
  withForeignPtr ez₁ $ \ ezp₁ →
    withForeignPtr ez₂ $ \ ezp₂ →
    newForeignPtr bit_destroy *$ integer_lt ezp₁ ezp₂

empIntegerCond ∷ ForeignPtr EMPBool → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerCond eb₁ ez₂ ez₃ = do
  withForeignPtr eb₁ $ \ ebp₁ →
    withForeignPtr ez₂ $ \ ezp₂ →
    withForeignPtr ez₃ $ \ ezp₃ →
    newForeignPtr integer_destroy *$ integer_cond ebp₁ ezp₂ ezp₃

foreign import ccall "empc.h integer_reveal" integer_reveal ∷ (Ptr EMPInt) → HS.Int → IO Int.Int64
foreign import ccall "empc.h bit_reveal" bit_reveal ∷ (Ptr EMPBool) → HS.Int → IO HS.Bool

empIntegerReveal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadIO m) ⇒ ForeignPtr EMPInt → 𝑃 PrinVal → m ℤ
empIntegerReveal ez ρvs = do
  party ← serializeMode (SecM ρvs)
  map HS.fromIntegral $ io $ withForeignPtr ez $ \ ezp → integer_reveal ezp party

empBitReveal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadIO m) ⇒ ForeignPtr EMPBool → 𝑃 PrinVal → m 𝔹
empBitReveal eb ρvs = do
  party ← serializeMode (SecM ρvs)
  io $ withForeignPtr eb $ \ ebp → bit_reveal ebp party
