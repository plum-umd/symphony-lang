module PSL.Interpreter.Circuits where

import UVMHS
import AddToUVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Lens
import PSL.Interpreter.Primitives

nextWire ∷ 𝑃 PrinVal → IM Wire
nextWire ρvs = nextL $ iStateNextWireL ρvs

inputWireMap ∷ Ckt → (Wire ⇰ Input)
inputWireMap = unionsUniq ∘ values ∘ inputsC

getWire ∷ Ckt → Wire → Input ∨ Gate
getWire ckt w = case (inputWireMap ckt) ⋕? w of
  None → case (access gatesCL ckt) ⋕? w of
    None → impossible
    Some g → Inr g
  Some i → Inl i

getOutput ∷ Ckt → Input ∨ Gate
getOutput ckt = getWire ckt $ outputC ckt

inputType ∷ Input → BaseType
inputType i = case i of
  AvailableI bv   → typeOfBaseVal bv
  UnavailableI bτ → bτ

wireType ∷ (STACK) ⇒ Ckt → Wire → BaseType
wireType ckt w = case getWire ckt w of
  Inl i → inputType i
  Inr g → case g of
    BaseG bv      → typeOfBaseVal bv
    PrimG op ws   → primType op $ mapOn ws $ wireType ckt

cktType ∷ (STACK) ⇒ Ckt → BaseType
cktType ckt = wireType ckt $ access outputCL ckt

mkCkt ∷ (STACK) ⇒ 𝑃 PrinVal → Gate → IM Ckt
mkCkt ρvs g = do
  output ← nextWire ρvs
  let c = Ckt { inputsC = dø, gatesC = (output ↦ g), outputC = output }
  return c

inputCkt ∷ (STACK) ⇒ 𝑃 PrinVal → PrinVal → Input → IM Ckt
inputCkt ρvs ρv i = do
  input ← nextWire ρvs
  let c = Ckt { inputsC = (ρv ↦ (input ↦ i)), gatesC = dø, outputC = input }
  return c

shareBaseValCkt ∷ (STACK) ⇒ 𝑃 PrinVal → PrinVal → BaseVal → IM Ckt
shareBaseValCkt ρvs ρv bv = inputCkt ρvs ρv (AvailableI bv)

shareUnkCkt ∷ (STACK) ⇒ 𝑃 PrinVal → PrinVal → BaseType → IM Ckt
shareUnkCkt ρvs ρv bτ = inputCkt ρvs ρv (UnavailableI bτ)

embedBaseValCkt ∷ (STACK) ⇒ 𝑃 PrinVal → BaseVal → IM Ckt
embedBaseValCkt ρvs bv = mkCkt ρvs (BaseG bv)

exePrimCkt ∷ (STACK) ⇒ 𝑃 PrinVal → Op → 𝐿 Ckt → IM Ckt
exePrimCkt ρvs op cs = do
  output ← nextWire ρvs
  let inputs' = unionsWith (⩌) $ (mapOn cs inputsC)
  let gates'  = foldOnFrom (mapOn cs gatesC) dø (⩌)
  return $ Ckt { inputsC = inputs', gatesC = gates' ⩌! (output ↦ (PrimG op $ mapOn cs outputC)), outputC = output }
