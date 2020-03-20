module PSL.Interpreter.Json where

import UVMHS
import PSL.Syntax
import PSL.Interpreter.Types

import qualified Data.Aeson as JSON

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
jsonEvent (ResEv φ ρs ρf ρt τ o) n =
  JSON.object [ "protocol" JSON..= stringProtocol φ 
              , "principals" JSON..= jsonPrins ρs
              , "prins_from" JSON..= jsonPrins ρf
              , "prins_to" JSON..= jsonPrins ρt
              , "type" JSON..= τ
              , "op" JSON..= o
              , "count" JSON..= n
              ]

jsonEvents ∷ (ToIter (ResEv ∧ ℕ) t) ⇒ t → JSON.Value
jsonEvents = JSON.toJSON ∘ lazyList ∘ map (\ (η :* n) → jsonEvent η n) ∘ iter
