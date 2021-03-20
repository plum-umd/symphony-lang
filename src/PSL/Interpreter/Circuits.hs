module PSL.Interpreter.Circuits where

import UVMHS
import AddToUVMHS

import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Lens
import PSL.Interpreter.Error
import PSL.Interpreter.Primitives
import PSL.Syntax

baseGateType ∷ BaseGate → Type
baseGateType bg = case bg of
  BoolBG   _ → 𝔹T
  NatBG pr _ → ℕT pr
  IntBG pr _ → ℤT pr
  FltBG pr _ → 𝔽T pr
  PrinBG   _ → ℙT

inputType ∷ Input → Type
inputType i = case i of
  AvailableI bg → baseGateType bg
  UnavailableI τ → τ

wireType ∷ (STACK) ⇒ Ckt → Wire → IM Type
wireType ckt w = do
  let gates = access gatesCL ckt
  g ← error𝑂 (gates ⋕? w) (throwIErrorCxt InternalIError "wireType: gates ⋕? w ≡ None" $ frhs
                         [ ("gates",pretty gates)
                         , ("w",pretty w)
                         ])
  case g of
    BaseG bg    → return $ baseGateType bg
    InputG _ρvs i → return $ inputType i
    PrimG op ws → do
      gτs ← mapMOn ws $ wireType ckt
      primType op gτs

cktType ∷ (STACK) ⇒ Ckt → IM Type
cktType ckt = do
  let output = access outCL ckt
  wireType ckt output

defaultCkt ∷ (STACK) ⇒ Type → IM Ckt
defaultCkt τ = do
  bg ← case τ of
         𝔹T    → return $ BoolBG False
         ℕT pr → return $ NatBG pr zero
         ℤT pr → return $ IntBG pr zero
         𝔽T pr → return $ FltBG pr zero
         ℙT    → return $ PrinBG BotBTD
         _     → throwIErrorCxt NotImplementedIError "defaultCkt" $ frhs
                 [ ("τ", pretty τ)
                 ]
  baseCkt bg

mkCkt ∷ (STACK) ⇒ Gate → IM Ckt
mkCkt g = do
  m ← askL iCxtGlobalModeL
  output ← nextL $ iStateNextWireL m
  let c = Ckt { gatesC = (output ↦ g), outC = output }
  pptraceM $ m :* c
  return c

baseCkt ∷ (STACK) ⇒ BaseGate → IM Ckt
baseCkt bg = mkCkt (BaseG bg)

inputCkt ∷ (STACK) ⇒ 𝑃 PrinVal → Input → IM Ckt
inputCkt ρvs i = mkCkt (InputG ρvs i)

boolCkt ∷ (STACK) ⇒ 𝔹 → IM Ckt
boolCkt b = baseCkt (BoolBG b)

boolInputCkt ∷ (STACK) ⇒ 𝑃 PrinVal → 𝔹 → IM Ckt
boolInputCkt ρvs b = inputCkt ρvs (AvailableI $ BoolBG b)

trueCkt ∷ (STACK) ⇒ IM Ckt
trueCkt = boolCkt True

trueInputCkt ∷ (STACK) ⇒ 𝑃 PrinVal → IM Ckt
trueInputCkt ρvs = boolInputCkt ρvs True

falseCkt ∷ (STACK) ⇒ IM Ckt
falseCkt = boolCkt False

falseInputCkt ∷ (STACK) ⇒ 𝑃 PrinVal → IM Ckt
falseInputCkt ρvs = boolInputCkt ρvs False

natCkt ∷ (STACK) ⇒ IPrecision → ℕ → IM Ckt
natCkt pr n = baseCkt (NatBG pr n)

natInputCkt ∷ (STACK) ⇒ 𝑃 PrinVal → IPrecision → ℕ → IM Ckt
natInputCkt ρvs pr n = inputCkt ρvs (AvailableI $ NatBG pr n)

intCkt ∷ (STACK) ⇒ IPrecision → ℤ → IM Ckt
intCkt pr i = baseCkt (IntBG pr i)

intInputCkt ∷ (STACK) ⇒ 𝑃 PrinVal → IPrecision → ℤ → IM Ckt
intInputCkt ρvs pr i = inputCkt ρvs (AvailableI $ IntBG pr i)

fltCkt ∷ (STACK) ⇒ FPrecision → 𝔻 → IM Ckt
fltCkt pr f = baseCkt (FltBG pr f)

fltInputCkt ∷ (STACK) ⇒ 𝑃 PrinVal → FPrecision → 𝔻 → IM Ckt
fltInputCkt ρvs pr f = inputCkt ρvs (AvailableI $ FltBG pr f)

prinCkt ∷ (STACK) ⇒ AddBTD PrinVal → IM Ckt
prinCkt btd = baseCkt (PrinBG btd)

prinInputCkt ∷ (STACK) ⇒ 𝑃 PrinVal → AddBTD PrinVal → IM Ckt
prinInputCkt ρvs btd = inputCkt ρvs (AvailableI $ PrinBG btd)

primCkt ∷ (STACK) ⇒ Op → 𝐿 Ckt → IM Ckt
primCkt op cs = do
  m ← askL iCxtGlobalModeL
  output ← nextL $ iStateNextWireL m
  let gates' = foldOnFrom (mapOn cs gatesC) dø (⩌)
  let args   = mapOn cs outC
  let c      = Ckt { gatesC = gates' ⩌ (output ↦ PrimG op args), outC = output }
  pptraceM $ m :* c
  return c

notCkt ∷ (STACK) ⇒ Ckt → IM Ckt
notCkt c = primCkt NotO $ frhs [ c ]

muxCkt ∷ (STACK) ⇒ Ckt → Ckt → Ckt → IM Ckt
muxCkt c₁ c₂ c₃ = primCkt CondO $ frhs [ c₁, c₂, c₃ ]

sumCkt ∷ (STACK) ⇒ Ckt → Ckt → IM Ckt
sumCkt c₁ c₂ = primCkt PlusO $ frhs [ c₁, c₂ ]

orCkt ∷ (STACK) ⇒ Ckt → Ckt → IM Ckt
orCkt c₁ c₂ = primCkt OrO $ frhs [ c₁, c₂ ]
