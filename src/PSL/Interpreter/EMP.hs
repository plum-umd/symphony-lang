module PSL.Interpreter.EMP where

import UVMHS
import AddToUVMHS

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

serializeMode ∷ (Monad m, MonadReader ICxt m, MonadError IError m) ⇒ 𝑃 PrinVal → Mode → m HS.Int
serializeMode ρvs = \case
  TopM     → impossibleM
  SecM ρvs → case list ρvs of
    ρv :& Nil     → map HS.fromIntegral $ fromSomeCxt $ ρvmap ⋕? ρv
    _ :& _ :& Nil → return $ HS.fromIntegral 0
    m             → throwIErrorCxt TypeIError "[Yao] serializeMode: only two parties allowed" $ frhs [ ("m", pretty m) ]
  where ρvmap = number𝐷 1 ρvs

serializePrec ∷ (Monad m, MonadReader ICxt m, MonadError IError m) ⇒ IPrecision → m HS.Int
serializePrec = \case
  FixedIPr 64 0 → return $ HS.fromIntegral 64
  pr → throwIErrorCxt NotImplementedIError "[Yao] serializePrec: precision pr not supported" $ frhs [ ("pr", pretty pr) ]

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

foreign import ccall "empc.h setup_semi_honest_c" setup_semi_honest_c ∷ NetIO → HS.Int → IO ()
foreign import ccall "empc.h finalize_semi_honest_c" finalize_semi_honest_c ∷ IO ()

setupEMP ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ 𝑃 PrinVal → HS.Int → m ()
setupEMP ρvsC party = do
  let addr = if isAlice party then None else Some localhost
  net ← io $ netIOCreate addr port
  io $ setup_semi_honest_c net party
  putL iStateYaoInitL True
  putL iStateYaoPartiesL ρvsC
  putL iStateYaoNetIOL net
  where localhost = "127.0.0.1"
        port      = HS.fromIntegral 12345
        isAlice p = p ≡ HS.fromIntegral 1

teardownEMP ∷ (Monad m, MonadReader ICxt m, MonadState IState m, MonadIO m) ⇒ m ()
teardownEMP = do
  net ← getL iStateYaoNetIOL
  io $ finalize_semi_honest_c
  io $ netio_destroy net
  putL iStateYaoInitL False

setupAndTeardown ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ 𝑃 PrinVal → HS.Int → m ()
setupAndTeardown ρvsC party = do
  initialized ← getL iStateYaoInitL
  if initialized then do
    ρvs ← getL iStateYaoPartiesL
    if ρvsC ≡ ρvs then return ()
    else teardownEMP
  else setupEMP ρvsC party

empType ∷ EMPVal → BaseType
empType = \case
  BoolEV   _ → 𝔹T
  NatEV pr _ → ℕT pr
  IntEV pr _ → ℤT pr
  FltEV pr _ → 𝔽T pr

foreign import ccall "empc.h bit_create" bit_create ∷ HS.Bool → HS.Int → IO (Ptr EMPBool)
foreign import ccall "empc.h &bit_destroy" bit_destroy ∷ FinalizerPtr EMPBool
foreign import ccall "empc.h integer_create" integer_create ∷ HS.Int → Int.Int64 → HS.Int → IO (Ptr EMPInt)
foreign import ccall "empc.h &integer_destroy" integer_destroy ∷ FinalizerPtr EMPInt

empShare ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ 𝑃 PrinVal → 𝑃 PrinVal → BaseVal → m EMPVal
empShare ρvsC ρvsS bv = do
  lm     ← askL iCxtLocalModeL
  me     ← serializeMode ρvsC lm
  pptraceM ρvsC
  pptraceM ρvsS
  setupAndTeardown ρvsC me
  sharer ← serializeMode ρvsC (SecM ρvsS)
  case bv of
    BoolBV b   → map BoolEV $ io $ newForeignPtr bit_destroy *$ bit_create b sharer
    NatBV pr n → do
      prec ← serializePrec pr
      map (NatEV pr) $ io $ newForeignPtr integer_destroy *$ integer_create prec (HS.fromIntegral n) sharer
    IntBV pr z → do
      prec ← serializePrec pr
      map (IntEV pr) $ io $ newForeignPtr integer_destroy *$ integer_create prec (HS.fromIntegral z) sharer
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
foreign import ccall "empc.h integer_gt" integer_gt ∷ (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPBool)
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

empIntegerGt ∷ ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPBool)
empIntegerGt ez₁ ez₂ = do
  pptraceM "GT"
  withForeignPtr ez₁ $ \ ezp₁ →
    withForeignPtr ez₂ $ \ ezp₂ →
    newForeignPtr bit_destroy *$ integer_gt ezp₁ ezp₂

empIntegerCond ∷ ForeignPtr EMPBool → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerCond eb₁ ez₂ ez₃ = do
  withForeignPtr eb₁ $ \ ebp₁ →
    withForeignPtr ez₂ $ \ ezp₂ →
    withForeignPtr ez₃ $ \ ezp₃ →
    newForeignPtr integer_destroy *$ integer_cond ebp₁ ezp₂ ezp₃

foreign import ccall "empc.h integer_reveal" integer_reveal ∷ (Ptr EMPInt) → HS.Int → IO Int.Int64
foreign import ccall "empc.h bit_reveal" bit_reveal ∷ (Ptr EMPBool) → HS.Int → IO HS.Bool

empIntegerReveal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadIO m) ⇒ ForeignPtr EMPInt → 𝑃 PrinVal → 𝑃 PrinVal → m ℤ
empIntegerReveal ez ρvsC ρvsR = do
  pptraceM ρvsC
  pptraceM ρvsR
  party ← serializeMode ρvsC (SecM ρvsR)
  map HS.fromIntegral $ io $ withForeignPtr ez $ \ ezp → integer_reveal ezp party

empBitReveal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadIO m) ⇒ ForeignPtr EMPBool → 𝑃 PrinVal → 𝑃 PrinVal → m 𝔹
empBitReveal eb ρvsC ρvsR = do
  party ← serializeMode ρvsC (SecM ρvsR)
  io $ withForeignPtr eb $ \ ebp → bit_reveal ebp party
