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
fprecisionSuffix (FixedFPr n₁ n₂) = concat ["#",show𝕊 n₁,".",show𝕊 n₂]

-- iPrecFrFPrec ∷ FPrecision → IPrecision
-- iPrecFrFPrec (FixedFPr pr) = FixedIPr pr 0

-- fPrecFrIPrec ∷ IPrecision → FPrecision
-- fPrecFrIPrec = \case
--   InfIPr → fprDefault
--   FixedIPr n₁ n₂ → FixedFPr $ n₁ + n₂

getType ∷ Val → 𝕊
getType = \case
  BaseV (BoolBV _) → "bool"
  BaseV (StrBV _) → "string"
  BaseV (NatBV p _) → "nat"⧺iprecisionSuffix p
  BaseV (IntBV p _) → "int"⧺iprecisionSuffix p
  BaseV (FltBV p _) → "flt"⧺fprecisionSuffix p
  BaseV BulBV → "bul"
  LV _ → "left"
  RV _ → "right"
  NilV → "list"
  ConsV _ _ → "list"
  CloV _ _ _ _ → "clo"
  TCloV _ _ _ → "tclo"
  BaseV (PrinBV _) → "prin"
  PrinSetV _ → "prinset"
  LocV _ _ → "loc"
  ArrayV _ → "array"
  PairV _ _ → "pair"
  DefaultV → "default"
  UnknownV _ → "unknown"

stringProtocol ∷ Prot → 𝕊
stringProtocol = \case
  Plain → "plain"
  YaoN_P → "yaoN_P"
  Yao2_P → "yao2_P"
  BGWP  → "bgw"
  GMWP  → "gmw"
  BGVP  → "bgv"
  SPDZP → "spdz"
  AutoP → "auto"

jsonPrinVal ∷ PrinVal → 𝕊
jsonPrinVal = \case
  SinglePV s → s
  AccessPV s i → s ⧺ "_" ⧺ show𝕊 i
  VirtualPV s → s

jsonPrins ∷ 𝑃 PrinVal → JSON.Value
jsonPrins = JSON.toJSON ∘ lazyList ∘ map jsonPrinVal ∘ iter

jsonEvent ∷ ResEv → ℕ → JSON.Value
jsonEvent (ResEv φ ρs ρf ρt τ τf τt o) n =
  JSON.object [ "protocol" JSON..= stringProtocol φ
              , "principals" JSON..= jsonPrins ρs
              , "prins_from" JSON..= jsonPrins ρf
              , "prins_to" JSON..= jsonPrins ρt
              , "type" JSON..= τ
              , "type_from" JSON..= τf
              , "type_to" JSON..= τt
              , "op" JSON..= o
              , "count" JSON..= n
              ]

jsonEvents ∷ (ToIter (ResEv ∧ ℕ) t) ⇒ t → JSON.Value
jsonEvents = JSON.toJSON ∘ lazyList ∘ map (\ (η :* n) → jsonEvent η n) ∘ iter
