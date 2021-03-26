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

inputType ∷ Input → BaseType
inputType i = case i of
  AvailableI bv   → typeOfBaseVal bv
  UnavailableI bτ → bτ

wireType ∷ (STACK) ⇒ Ckt → Wire → BaseType
wireType ckt w = case g of
  BaseG bv      → typeOfBaseVal bv
  InputG _ρv i  → inputType i
  PrimG op ws   → primType op $ mapOn ws $ wireType ckt
  where g = impFromSome $ (access gatesCL ckt) ⋕? w

cktType ∷ (STACK) ⇒ Ckt → BaseType
cktType ckt = wireType ckt $ access outCL ckt

mkCkt ∷ (STACK) ⇒ 𝑃 PrinVal → Gate → IM Ckt
mkCkt ρvs g = do
  output ← nextWire ρvs
  let c = Ckt { gatesC = (output ↦ g), outC = output }
  return c

inputCkt ∷ (STACK) ⇒ 𝑃 PrinVal → PrinVal → Input → IM Ckt
inputCkt ρvs ρv i = mkCkt ρvs (InputG ρv i)

shareBaseValCkt ∷ (STACK) ⇒ 𝑃 PrinVal → PrinVal → BaseVal → IM Ckt
shareBaseValCkt ρvs ρv bv = inputCkt ρvs ρv (AvailableI bv)

shareUnkCkt ∷ (STACK) ⇒ 𝑃 PrinVal → PrinVal → BaseType → IM Ckt
shareUnkCkt ρvs ρv bτ = inputCkt ρvs ρv (UnavailableI bτ)

embedBaseValCkt ∷ (STACK) ⇒ 𝑃 PrinVal → BaseVal → IM Ckt
embedBaseValCkt ρvs bv = mkCkt ρvs (BaseG bv)

exePrimCkt ∷ (STACK) ⇒ 𝑃 PrinVal → Op → 𝐿 Ckt → IM Ckt
exePrimCkt ρvs op cs = do
  output ← nextWire ρvs
  let gates' = foldOnFrom (mapOn cs gatesC) dø (⩌)
  let args   = mapOn cs outC
  return $ Ckt { gatesC = gates' ⩌ (output ↦ PrimG op args), outC = output }
