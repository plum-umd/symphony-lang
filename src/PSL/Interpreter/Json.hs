module PSL.Interpreter.Json where

import UVMHS
import PSL.Syntax
import PSL.Interpreter.Types

import qualified Data.Aeson as JSON

iprecisionSuffix ∷ IPrecision → 𝕊
iprecisionSuffix = \case
  InfIPr → ""
  FixedIPr n₁ n₂ → concat ["#",show𝕊 n₁,".",show𝕊 n₂]

fprecisionSuffix ∷ FPrecision → 𝕊
fprecisionSuffix (FixedFPr n) = concat ["#",show𝕊 n]

iPrecFrFPrec ∷ FPrecision → IPrecision
iPrecFrFPrec (FixedFPr pr) = FixedIPr pr 0

fPrecFrIPrec ∷ IPrecision → FPrecision
fPrecFrIPrec = \case
  InfIPr → FixedFPr 64
  FixedIPr n₁ n₂ → FixedFPr $ n₁ + n₂

getType ∷ Val → 𝕊
getType = \case
  BoolV _ → "bool"
  StrV _ → "string"
  NatV p _ → "nat"⧺iprecisionSuffix p
  IntV p _ → "int"⧺iprecisionSuffix p
  FltV p _ → "flt"⧺fprecisionSuffix p
  BulV → "bul"
  LV _ → "left"
  RV _ → "right"
  -- PairV _ _ → "pair"
  NilV → "list"
  ConsV _ _ → "list"
  CloV _ _ _ _ → "clo"
  TCloV _ _ _ → "tclo"
  PrinV _ → "prin"
  PrinSetV _ → "prinset"
  LocV _ → "loc"
  ArrayV _ → "array"
  PairV _ _ → "pair"

getTypeMPC ∷ ValMPC → 𝕊
getTypeMPC = \case
  BoolMV _ → "bool"
  NatMV p _ → "nat"⧺iprecisionSuffix p
  IntMV p _ → "int"⧺iprecisionSuffix p
  FltMV p _ → "flt"⧺fprecisionSuffix p
  PrinMV _ → "prin"
  PairMV mv₁ mv₂ → (getTypeMPC mv₁) ⧺ " × " ⧺ (getTypeMPC mv₂)
  LMV mv → "left " ⧺ (getTypeMPC mv)
  RMV mv → "right " ⧺ (getTypeMPC mv)


stringProtocol ∷ Prot → 𝕊
stringProtocol = \case
  YaoP  → "yao"
  BGWP  → "bgw"
  GMWP  → "gmw"
  BGVP  → "bgv"
  SPDZP → "spdz"

jsonPrinVal ∷ PrinVal → 𝕊
jsonPrinVal = \case
  SinglePV s → s
  AccessPV s i → s ⧺ "_" ⧺ show𝕊 i

jsonPrins ∷ 𝑃 PrinVal → JSON.Value
jsonPrins = JSON.toJSON ∘ lazyList ∘ map jsonPrinVal ∘ iter

jsonEvent ∷ ResEv → ℕ → JSON.Value
jsonEvent (ResEv φ ρs ρf ρt τ o md) n =
  JSON.object [ "protocol" JSON..= stringProtocol φ 
              , "principals" JSON..= jsonPrins ρs
              , "prins_from" JSON..= jsonPrins ρf
              , "prins_to" JSON..= jsonPrins ρt
              , "type" JSON..= τ
              , "op" JSON..= o
              , "md" JSON..= md
              , "count" JSON..= n
              ]

jsonEvents ∷ (ToIter (ResEv ∧ ℕ) t) ⇒ t → JSON.Value
jsonEvents = JSON.toJSON ∘ lazyList ∘ map (\ (η :* n) → jsonEvent η n) ∘ iter
