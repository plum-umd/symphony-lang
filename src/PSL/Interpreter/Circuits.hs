module PSL.Interpreter.Circuits where

import UVMHS
import AddToUVMHS

import PSL.Interpreter.Types
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

muxCktVal ∷ (STACK) ⇒ Ckt → CktVal → CktVal → IM CktVal
muxCktVal c₁ cv₂ cv₃ =
  case (cv₂, cv₃) of
  (DefaultCV, DefaultCV) → return DefaultCV
  (DefaultCV, BaseCV c₃) → do
    τ₂ ← cktType c₃
    c₂ ← defaultCkt τ₂
    c' ← muxCkt c₁ c₂ c₃
    return $ BaseCV c'
  (BaseCV c₂, DefaultCV) → do
    τ₃ ← cktType c₂
    c₃ ← defaultCkt τ₃
    c' ← muxCkt c₁ c₂ c₃
    return $ BaseCV c'
  (BaseCV c₂, BaseCV c₃) → do
    c' ← muxCkt c₁ c₂ c₃
    return $ BaseCV c'
  (DefaultCV, PairCV cv₃₁ cv₃₂) → do
    cv'₁ ← muxCktVal c₁ DefaultCV cv₃₁
    cv'₂ ← muxCktVal c₁ DefaultCV cv₃₂
    return $ PairCV cv'₁ cv'₂
  (PairCV cv₂₁ cv₂₂, DefaultCV) → do
    cv'₁ ← muxCktVal c₁ cv₂₁ DefaultCV
    cv'₂ ← muxCktVal c₁ cv₂₂ DefaultCV
    return $ PairCV cv'₁ cv'₂
  (PairCV cv₂₁ cv₂₂, PairCV cv₃₁ cv₃₂) → do
    cv'₁ ← muxCktVal c₁ cv₂₁ cv₃₁
    cv'₂ ← muxCktVal c₁ cv₂₂ cv₃₂
    return $ PairCV cv'₁ cv'₂
  (DefaultCV, SumCV c₃ cv₃₁ cv₃₂) → do
    def ← defaultCkt 𝔹T
    c' ← muxCkt c₁ def c₃
    cv'₁ ← muxCktVal c₁ DefaultCV cv₃₁
    cv'₂ ← muxCktVal c₁ DefaultCV cv₃₂
    return $ SumCV c' cv'₁ cv'₂
  (SumCV c₂ cv₂₁ cv₂₂, DefaultCV) → do
    def ← defaultCkt 𝔹T
    c' ← muxCkt c₁ c₂ def
    cv'₁ ← muxCktVal c₁ cv₂₁ DefaultCV
    cv'₂ ← muxCktVal c₁ cv₂₂ DefaultCV
    return $ SumCV c' cv'₁ cv'₂
  (SumCV c₂ cv₂₁ cv₂₂, SumCV c₃ cv₃₁ cv₃₂) → do
    c' ← muxCkt c₁ c₂ c₃
    cv'₁ ← muxCktVal c₁ cv₂₁ cv₃₁
    cv'₂ ← muxCktVal c₁ cv₂₂ cv₃₂
    return $ SumCV c' cv'₁ cv'₂
  (DefaultCV, NilCV) → return NilCV
  (NilCV, DefaultCV) → return NilCV
  (NilCV, NilCV) → return NilCV
  (DefaultCV, ConsCV cv₃₁ cv₃₂) → do
    cv'₁ ← muxCktVal c₁ DefaultCV cv₃₁
    cv'₂ ← muxCktVal c₁ DefaultCV cv₃₂
    return $ ConsCV cv'₁ cv'₂
  (ConsCV cv₂₁ cv₂₂, DefaultCV) → do
    cv'₁ ← muxCktVal c₁ cv₂₁ DefaultCV
    cv'₂ ← muxCktVal c₁ cv₂₂ DefaultCV
    return $ ConsCV cv'₁ cv'₂
  (ConsCV cv₂₁ cv₂₂, ConsCV cv₃₁ cv₃₂) → do
    cv'₁ ← muxCktVal c₁ cv₂₁ cv₃₁
    cv'₂ ← muxCktVal c₁ cv₂₂ cv₃₂
    return $ ConsCV cv'₁ cv'₂
  (DefaultCV, BulCV) → return BulCV
  (BulCV, DefaultCV) → return BulCV
  (BulCV, BulCV) → return BulCV
  _ → throwIErrorCxt TypeIError "muxCktVal: circuit values cv₂ and cv₃ have different shapes." $ frhs
    [ ("cv₂", pretty cv₂)
    , ("cv₃", pretty cv₃)
    ]

sumCktVal ∷ (STACK) ⇒ CktVal → CktVal → IM CktVal
sumCktVal cv₁ cv₂ = case (cv₁,cv₂) of
  (_, DefaultCV) → return cv₁
  (DefaultCV, _) → return cv₂
  (BaseCV c₁, BaseCV c₂) → do
    c' ← sumCkt c₁ c₂
    return $ BaseCV c'
  (PairCV cv₁₁ cv₁₂, PairCV cv₂₁ cv₂₂) → do
    cv'₁ ← sumCktVal cv₁₁ cv₂₁
    cv'₂ ← sumCktVal cv₁₂ cv₂₂
    return $ PairCV cv'₁ cv'₂
  (SumCV c₁ cv₁₁ cv₁₂, SumCV c₂ cv₂₁ cv₂₂) → do
    c' ← orCkt c₁ c₂
    cv'₁ ← sumCktVal cv₁₁ cv₂₁
    cv'₂ ← sumCktVal cv₁₂ cv₂₂
    return $ SumCV c' cv'₁ cv'₂
  (NilCV, NilCV) → return NilCV
  (ConsCV cv₁₁ cv₁₂, ConsCV cv₂₁ cv₂₂) → do
    cv'₁ ← sumCktVal cv₁₁ cv₂₁
    cv'₂ ← sumCktVal cv₁₂ cv₂₂
    return $ ConsCV cv'₁ cv'₂
  (BulCV, BulCV) → return BulCV
  _ → throwIErrorCxt TypeIError "sumCktVal: circuit values cv₁ and cv₂ have different shapes." $ frhs
    [ ("cv₁", pretty cv₁)
    , ("cv₂", pretty cv₂)
    ]

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
