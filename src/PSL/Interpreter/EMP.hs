module PSL.Interpreter.EMP where

import UVMHS
import PSL.Syntax
import PSL.Interpreter.Types

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.String

import qualified Prelude as HS

{- NetIO, C++ channel EMP uses to communicate between parties -}
data NetIOStruct = NetIOStruct
type NetIO = Ptr NetIOStruct -- Cannot be ForeignPtr because EMP holds an internal reference

foreign import ccall "empc.h netio_create" netio_create ∷ CString → HS.Int → IO NetIO
foreign import ccall "empc.h netio_destroy" netio_destroy ∷ NetIO → IO ()
netIOCreate ∷ 𝑂 𝕊 → ℤ64 → IO NetIO
netIOCreate None port = netio_create nullPtr (tohs port)
netIOCreate (Some addr) port = withCString (chars addr) $ \ caddr → netio_create caddr (tohs port)

netIODestroy ∷ NetIO → IO ()
netIODestroy = netio_destroy

foreign import ccall "empc.h setup_semi_honest_c" setup_semi_honest_c ∷ NetIO → HS.Int → IO ()

normParty ∷ Prin → Prin
normParty = string ∘ (\ c → [c]) ∘ toUpper ∘ HS.head ∘ chars

parseParty ∷ Prin → IO HS.Int
parseParty party = case normParty party of
  "A" → return $ HS.fromIntegral 1
  "B" → return $ HS.fromIntegral 2
  _   → failIO "parseParty: EMP: party ∉ { Alice, Bob }"

setupSemiHonest ∷ NetIO → Prin → IO ()
setupSemiHonest net party = do
  party ← parseParty party
  setup_semi_honest_c net (tohs party)

foreign import ccall "empc.h integer_create" integer_create ∷ HS.Int → CString → HS.Int → IO (Ptr IntEMPS)
foreign import ccall "empc.h integer_add" integer_add ∷ (Ptr IntEMPS) → (Ptr IntEMPS) → IO (Ptr IntEMPS)
foreign import ccall "empc.h integer_reveal" integer_reveal ∷ (Ptr IntEMPS) → HS.Int → IO HS.Int
foreign import ccall "empc.h &integer_destroy" integer_destroy ∷ FinalizerPtr IntEMPS

checkPrec ∷ IPrecision → IM HS.Int
checkPrec InfIPr = throwIErrorCxt TypeIError "checkPrec: EMP: ∞ precision unsupported." empty𝐿
checkPrec (FixedIPr whole _) = return $ HS.fromIntegral whole

integerCreate ∷ IPrecision → ℤ → Prin → IM IntEMP
integerCreate prec z party = do
  ptr ← integerCreate' prec z party
  io $ newForeignPtr integer_destroy ptr

integerCreate' ∷ IPrecision → ℤ → Prin → IM (Ptr IntEMPS)
integerCreate' prec z party = do
  party ← io $ parseParty party
  prec ← checkPrec prec
  io $ withCString (show z) $ \ csz → integer_create prec csz (tohs party)

integerAdd ∷ IntEMP → IntEMP → IO IntEMP
integerAdd lhs rhs =
  withForeignPtr lhs $ \ lhsptr →
    withForeignPtr rhs $ \ rhsptr → do
      ptr ← integer_add lhsptr rhsptr
      newForeignPtr integer_destroy ptr

public ∷ 𝑃 Prin
public = (single𝑃 "A") ∪ (single𝑃 "B")

integerReveal ∷ IntEMP → 𝑃 Prin → IM ℤ
integerReveal share ρvs = do
  party ← if (count ρvs ≡ 1) --todo(ins): assumes ρvs ≡ (single𝑃 "A") or ρvs ≡ (single𝑃 "B")
          then do
            let Some (party :* _) = pmin ρvs
            io $ parseParty party
          else do --todo(ins): currently assumes ρvs ≡ public
            let party = HS.fromIntegral 0 -- 0 is EMP party identifier for public (A and B)
            return party
  io $ withForeignPtr share $ \ shareptr → do
    n ← integer_reveal shareptr party
    return $ HS.fromIntegral n
