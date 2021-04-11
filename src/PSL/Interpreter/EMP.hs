module PSL.Interpreter.EMP where

import UVMHS
import AddToUVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Lens
import PSL.Interpreter.Error
import PSL.Interpreter.Send (whoAmI)

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.String

import Network.Socket (PortNumber)

import qualified Prelude as HS
import qualified Data.Int as Int
import qualified Data.Text as Text

--------------------------
--- Serializing to EMP ---
--------------------------

serializePrin ∷ (Monad m, MonadReader ICxt m, MonadError IError m) ⇒ 𝑃 PrinVal → PrinVal → m HS.Int
serializePrin ρvs ρv = map HS.fromIntegral $ fromSomeCxt $ ρvmap ⋕? ρv
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

portEMP ∷ PortNumber
portEMP = HS.fromIntegral 12345

foreign import ccall "empc.h setup_semi_honest_c" setup_semi_honest_c ∷ NetIO → HS.Int → IO SemiHonest
foreign import ccall "empc.h finalize_semi_honest_c" finalize_semi_honest_c ∷ SemiHonest → IO ()

setupEMP ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ 𝑃 PrinVal → HS.Int → PrinVal → m ()
setupEMP ρvsC me other = do
  sessions ← getL iStateSessionsYaoL
  when (sessions ⋕? other ≡ None) $ do
    portMap ← getPortMap portEMP
    ρvCanon :* _ ← fromSomeCxt $ pmin ρvsC
    port ← map HS.fromIntegral $ fromSomeCxt $ portMap ⋕? ρvCanon
    let addr = if isAlice me then None else Some localhost
    net ← io $ netIOCreate addr port
    sh  ← io $ setup_semi_honest_c net me
    let sess = EMPSession { channelES = net , semiHonestES = sh }
    modifyL iStateSessionsYaoL ((other ↦ sess) ⩌!)
  where localhost = "127.0.0.1"
        isAlice p = p ≡ HS.fromIntegral 1

teardownEMP ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ PrinVal → m ()
teardownEMP ρv = do
  sessions ← getL iStateSessionsYaoL
  sess ← fromSomeCxt $ sessions ⋕? ρv
  io $ finalize_semi_honest_c $ semiHonestES sess
  io $ netio_destroy $ channelES sess
  putL iStateSessionsYaoL (delete ρv sessions)

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
  me     ← whoAmI
  meEmp  ← serializePrin ρvsC me
  other  ← fromSomeCxt $ view one𝑃L $ ρvsC ∖ (single𝑃 me)
  setupEMP ρvsC meEmp other
  sharer ← elim𝑂 (return $ HS.fromIntegral 0) (serializePrin ρvsC) $ view one𝑃L ρvsS
  case bv of
    BoolBV b   → map BoolEV $ io $ newForeignPtr bit_destroy *$ bit_create b sharer
    NatBV pr n → do
      prec ← serializePrec pr
      map (NatEV pr) $ io $ newForeignPtr integer_destroy *$ integer_create prec (HS.fromIntegral n) sharer
    IntBV pr z → do
      prec ← serializePrec pr
      map (IntEV pr) $ io $ newForeignPtr integer_destroy *$ integer_create prec (HS.fromIntegral z) sharer
    FltBV pr f → throwIErrorCxt NotImplementedIError "[Yao] empShare: 𝔻 (Float) not implemented" empty𝐿

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

foreign import ccall "empc.h bit_not" bit_not ∷ (Ptr EMPBool) → IO (Ptr EMPBool)
foreign import ccall "empc.h bit_and" bit_and ∷ (Ptr EMPBool) → (Ptr EMPBool) → IO (Ptr EMPBool)
foreign import ccall "empc.h bit_cond" bit_cond ∷ (Ptr EMPBool) → (Ptr EMPBool) → (Ptr EMPBool) → IO (Ptr EMPBool)

empBitNot ∷ ForeignPtr EMPBool → IO (ForeignPtr EMPBool)
empBitNot eb₁ = empUnary eb₁ bit_not bit_destroy

empBitAnd ∷ ForeignPtr EMPBool → ForeignPtr EMPBool → IO (ForeignPtr EMPBool)
empBitAnd eb₁ eb₂ = empBinary eb₁ eb₂ bit_and bit_destroy

empBitCond ∷ ForeignPtr EMPBool → ForeignPtr EMPBool → ForeignPtr EMPBool → IO (ForeignPtr EMPBool)
empBitCond eb₁ eb₂ eb₃ = empTernary eb₁ eb₂ eb₃ bit_cond bit_destroy

foreign import ccall "empc.h integer_add" integer_add ∷ (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)
foreign import ccall "empc.h integer_sub" integer_sub ∷ (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)
foreign import ccall "empc.h integer_mult" integer_mult ∷ (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)
foreign import ccall "empc.h integer_div" integer_div ∷ (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)
foreign import ccall "empc.h integer_mod" integer_mod ∷ (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)
foreign import ccall "empc.h integer_eq" integer_eq ∷ (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPBool)
foreign import ccall "empc.h integer_lt" integer_lt ∷ (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPBool)
foreign import ccall "empc.h integer_gt" integer_gt ∷ (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPBool)
foreign import ccall "empc.h integer_cond" integer_cond ∷ (Ptr EMPBool) → (Ptr EMPInt) → (Ptr EMPInt) → IO (Ptr EMPInt)

empIntegerAdd ∷ ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerAdd ez₁ ez₂ = empBinary ez₁ ez₂ integer_add integer_destroy

empIntegerSub ∷ ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerSub ez₁ ez₂ = empBinary ez₁ ez₂ integer_sub integer_destroy

empIntegerMult ∷ ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerMult ez₁ ez₂ = empBinary ez₁ ez₂ integer_mult integer_destroy

empIntegerDiv ∷ ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerDiv ez₁ ez₂ = empBinary ez₁ ez₂ integer_div integer_destroy

empIntegerMod ∷ ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerMod ez₁ ez₂ = empBinary ez₁ ez₂ integer_mod integer_destroy

empIntegerEq ∷ ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPBool)
empIntegerEq ez₁ ez₂ = empBinary ez₁ ez₂ integer_eq bit_destroy

empIntegerLt ∷ ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPBool)
empIntegerLt ez₁ ez₂ = empBinary ez₁ ez₂ integer_lt bit_destroy

empIntegerGt ∷ ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPBool)
empIntegerGt ez₁ ez₂ = empBinary ez₁ ez₂ integer_gt bit_destroy

empIntegerCond ∷ ForeignPtr EMPBool → ForeignPtr EMPInt → ForeignPtr EMPInt → IO (ForeignPtr EMPInt)
empIntegerCond eb₁ ez₂ ez₃ = empTernary eb₁ ez₂ ez₃ integer_cond integer_destroy

foreign import ccall "empc.h integer_reveal" integer_reveal ∷ (Ptr EMPInt) → HS.Int → IO Int.Int64
foreign import ccall "empc.h bit_reveal" bit_reveal ∷ (Ptr EMPBool) → HS.Int → IO HS.Bool

empIntegerReveal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadIO m) ⇒ ForeignPtr EMPInt → 𝑃 PrinVal → PrinVal → m ℤ
empIntegerReveal ez ρvsC ρvR = do
  party ← serializePrin ρvsC ρvR
  map HS.fromIntegral $ io $ withForeignPtr ez $ \ ezp → integer_reveal ezp party

empBitReveal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadIO m) ⇒ ForeignPtr EMPBool → 𝑃 PrinVal → PrinVal → m 𝔹
empBitReveal eb ρvsC ρvR = do
  party ← serializePrin ρvsC ρvR
  io $ withForeignPtr eb $ \ ebp → bit_reveal ebp party
