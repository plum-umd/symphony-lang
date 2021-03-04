module PSL.Interpreter.Circuits where

import UVMHS
import AddToUVMHS

import PSL.Interpreter.Types
import PSL.Interpreter.Primitives
import PSL.Syntax

baseCkt ∷ (STACK) ⇒ BaseCkt → IM Ckt
baseCkt bc = do
  o ← nextL iStateNextWireL
  return $ Ckt { inputs = empty𝐿, gates = o ↦ (BaseG bc), output = o, typ = typeOfBaseCkt bc }

defaultCkt ∷ (STACK) ⇒ Type → IM Ckt
defaultCkt τ =
  let bc = case τ of
        𝔹T    → BoolBC False
        ℕT pr → NatBC pr zero
        ℤT pr → IntBC pr zero
        𝔽T pr → FltBC pr zero
        ℙT    → PrinBC BotBTD
  in
  baseCkt bc

boolCkt ∷ (STACK) ⇒ 𝔹 → IM Ckt
boolCkt b = baseCkt (BoolBC b)

trueCkt ∷ (STACK) ⇒ IM Ckt
trueCkt = boolCkt True

falseCkt ∷ (STACK) ⇒ IM Ckt
falseCkt = boolCkt False

natCkt ∷ (STACK) ⇒ IPrecision → ℕ → IM Ckt
natCkt pr n = baseCkt (NatBC pr n)

intCkt ∷ (STACK) ⇒ IPrecision → ℤ → IM Ckt
intCkt pr i = baseCkt (IntBC pr i)

fltCkt ∷ (STACK) ⇒ FPrecision → 𝔻 → IM Ckt
fltCkt pr i = baseCkt (FltBC pr i)

prinCkt ∷ (STACK) ⇒ AddBTD PrinVal → IM Ckt
prinCkt btd = baseCkt (PrinBC btd)

muxCktVal ∷ (STACK) ⇒ Ckt → CktVal → CktVal → IM CktVal
muxCktVal c₁ cv₂ cv₃ = case (cv₂, cv₃) of
  (DefaultCV, DefaultCV) → return DefaultCV
  (DefaultCV, BaseCV c₃) → do
    c₂ ← defaultCkt (typ c₃)
    c' ← muxCkt c₁ c₂ c₃
    return $ BaseCV c'
  (BaseCV c₂, DefaultCV) → do
    c₃ ← defaultCkt (typ c₂)
    c' ← muxCkt c₁ c₂ c₃
    return $ BaseCV c'
  (BaseCV c₂, BaseCV c₃) → do
    c' ← muxCkt c₁ c₂ c₃
    return $ BaseCV c'

sumCktVal ∷ (STACK) ⇒ CktVal → CktVal → IM CktVal
sumCktVal cv₁ cv₂ = case (cv₁,cv₂) of
  (cv₁, DefaultCV) → return cv₁
  (DefaultCV, cv₂) → return cv₂
  (BaseCV c₁, BaseCV c₂) → do
    c' ← sumCkt c₁ c₂
    return $ BaseCV c'
  (PairCV cv₁₁ cv₁₂, PairCV cv₂₁ cv₂₂) → do
    cv₁' ← sumCktVal cv₁₁ cv₂₁
    cv₂' ← sumCktVal cv₁₂ cv₂₂
    return $ PairCV cv₁' cv₂'

inputCkt ∷ (STACK) ⇒ 𝑃 PrinVal → Type → IM Ckt
inputCkt ρvs τ = do
  o ← nextL iStateNextWireL
  return $ Ckt { inputs = frhs [ o :* ρvs ], gates = dø, output = o, typ = τ }

primCkt ∷ (STACK) ⇒ Op → 𝐿 Ckt → IM Ckt
primCkt op cs = do
  o ← nextL iStateNextWireL
  let inputs' = list $ uniques $ concat $ mapOn cs inputs
  let gates'  = (o ↦ (PrimG op $ mapOn cs output)) ⩌ (unionsWith (\ g₁ _ → g₁) $ mapOn cs gates)
  typ' ← primType op $ mapOn cs typ
  return $ Ckt { inputs = inputs', gates = gates', output = o, typ = typ' }

notCkt ∷ (STACK) ⇒ Ckt → IM Ckt
notCkt c = primCkt NotO $ frhs [ c ]

muxCkt ∷ (STACK) ⇒ Ckt → Ckt → Ckt → IM Ckt
muxCkt c₁ c₂ c₃= primCkt CondO $ frhs [ c₁, c₂, c₃ ]

sumCkt ∷ (STACK) ⇒ Ckt → Ckt → IM Ckt
sumCkt c₁ c₂ = primCkt PlusO $ frhs [ c₁, c₂ ]
