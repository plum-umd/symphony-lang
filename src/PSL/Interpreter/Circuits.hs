module PSL.Interpreter.Circuits where

import UVMHS
import AddToUVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Lens
import PSL.Interpreter.Primitives

nextWire ∷ IM Wire
nextWire = do
  gm ← askL iCxtGlobalModeL
  nextL $ iStateNextWireL gm

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

mkCkt ∷ (STACK) ⇒ Gate → IM Ckt
mkCkt g = do
  output ← nextWire
  let c = Ckt { gatesC = (output ↦ g), outC = output }
  return c

inputCkt ∷ (STACK) ⇒ PrinVal → Input → IM Ckt
inputCkt ρv i = mkCkt (InputG ρv i)

shareBaseValCkt ∷ (STACK) ⇒ PrinVal → BaseVal → IM Ckt
shareBaseValCkt ρv bv = inputCkt ρv (AvailableI bv)

shareUnkCkt ∷ (STACK) ⇒ PrinVal → BaseType → IM Ckt
shareUnkCkt ρv bτ = inputCkt ρv (UnavailableI bτ)

embedBaseValCkt ∷ (STACK) ⇒ BaseVal → IM Ckt
embedBaseValCkt bv = mkCkt (BaseG bv)

exePrimCkt ∷ (STACK) ⇒ Op → 𝐿 Ckt → IM Ckt
exePrimCkt op cs = do
  m ← askL iCxtGlobalModeL
  output ← nextL $ iStateNextWireL m
  let gates' = foldOnFrom (mapOn cs gatesC) dø (⩌)
  let args   = mapOn cs outC
  return $ Ckt { gatesC = gates' ⩌ (output ↦ PrimG op args), outC = output }
