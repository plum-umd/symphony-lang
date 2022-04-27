module Symphony.Dynamic.Par.Primitives where

import Symphony.Prelude

import Symphony.Lang.Syntax

import Symphony.Dynamic.Par.Types
import Symphony.Dynamic.Par.Truncating
import Symphony.Dynamic.Par.Error

import Symphony.Dynamic.Par.GMW

primBaseVal ∷ Op → 𝐿 BaseVal → IM Val BaseVal
primBaseVal op bvs = case (op, tohs bvs) of
  -- Booleans
  (NotO, [ BoolV (ClearBV b) ]) → return $ BoolV $ ClearBV $ not b

  (AndO, [ BoolV (ClearBV b₁), BoolV (ClearBV b₂) ]) → return $ BoolV $ ClearBV $ b₁ ⩓ b₂
  (OrO , [ BoolV (ClearBV b₁), BoolV (ClearBV b₂) ]) → return $ BoolV $ ClearBV $ b₁ ⩔ b₂
  (EqO , [ BoolV (ClearBV b₁), BoolV (ClearBV b₂) ]) → return $ BoolV $ ClearBV $ b₁ ≡ b₂

  (AndO, [ BoolV (ClearBV b₁), BoolV (EncBV ρvs₂ (GmwB b₂)) ]) → BoolV ^$ EncBV ρvs₂ ^$ GmwB ^$ do
    gmw ← getOrMkGmw ρvs₂
    b₁  ← gmwBoolConstant gmw b₁
    gmwBoolAnd gmw b₁ b₂

  (CondO, [ BoolV (ClearBV b), BoolV (ClearBV b₁), BoolV (ClearBV b₂) ]) → return $ BoolV $ ClearBV $ if b then b₁ else b₂

  -- Naturals
  (NatO pr₁, [ NatV _ (ClearNV n) ]) → return $ NatV pr₁ $ ClearNV $ trPrNat pr₁ n
  (IntO pr₁, [ NatV _ (ClearNV n) ]) → return $ IntV pr₁ $ ClearZV $ trPrInt pr₁ $ int n

  (PlusO , [ NatV pr₁ (ClearNV n₁), NatV pr₂ (ClearNV n₂) ]) | pr₁ ≡ pr₂ → return $ NatV pr₁ $ ClearNV $ trPrNat pr₁ $ n₁ + n₂
  (MinusO, [ NatV pr₁ (ClearNV n₁), NatV pr₂ (ClearNV n₂) ]) | pr₁ ≡ pr₂ → return $ NatV pr₁ $ ClearNV $ trPrNat pr₁ $ buPrNat pr₁ $ n₁ - n₂
  (TimesO, [ NatV pr₁ (ClearNV n₁), NatV pr₂ (ClearNV n₂) ]) | pr₁ ≡ pr₂ → return $ NatV pr₁ $ ClearNV $ trPrNat pr₁ $ n₁ × n₂
  (ExpO  , [ NatV pr₁ (ClearNV n₁), NatV pr₂ (ClearNV n₂) ]) | pr₁ ≡ pr₂ → return $ NatV pr₁ $ ClearNV $ trPrNat pr₁ $ n₁ ^^ n₂
  (DivO  , [ NatV pr₁ (ClearNV n₁), NatV pr₂ (ClearNV n₂) ]) | pr₁ ≡ pr₂ → return $ NatV pr₁ $ ClearNV $ trPrNat pr₁ $ if n₂ ≡ 0 then n₁ else n₁ ⌿ n₂
  (ModO  , [ NatV pr₁ (ClearNV n₁), NatV pr₂ (ClearNV n₂) ]) | pr₁ ≡ pr₂ → return $ NatV pr₁ $ ClearNV $ trPrNat pr₁ $ if n₂ ≡ 0 then n₁ else n₁ ÷ n₂
  (EqO   , [ NatV pr₁ (ClearNV n₁), NatV pr₂ (ClearNV n₂) ]) | pr₁ ≡ pr₂ → return $ BoolV    $ ClearBV $ n₁ ≡ n₂
  (LTO   , [ NatV pr₁ (ClearNV n₁), NatV pr₂ (ClearNV n₂) ]) | pr₁ ≡ pr₂ → return $ BoolV    $ ClearBV $ n₁ < n₂
  (LTEO  , [ NatV pr₁ (ClearNV n₁), NatV pr₂ (ClearNV n₂) ]) | pr₁ ≡ pr₂ → return $ BoolV    $ ClearBV $ n₁ ≤ n₂
  (GTO   , [ NatV pr₁ (ClearNV n₁), NatV pr₂ (ClearNV n₂) ]) | pr₁ ≡ pr₂ → return $ BoolV    $ ClearBV $ n₁ > n₂
  (GTEO  , [ NatV pr₁ (ClearNV n₁), NatV pr₂ (ClearNV n₂) ]) | pr₁ ≡ pr₂ → return $ BoolV    $ ClearBV $ n₁ ≥ n₂

  (CondO, [ BoolV (ClearBV b), NatV pr₁ (ClearNV n₁), NatV pr₂ (ClearNV n₂) ]) | pr₁ ≡ pr₂ → return $ NatV pr₁ $ ClearNV $ if b then n₁ else n₂

  -- Integers
  (NatO pr₁, [ IntV _  (ClearZV i) ]) → return $ NatV pr₁ $ ClearNV $ trPrNat pr₁ $ natΩ i
  (IntO pr₁, [ IntV _  (ClearZV i) ]) → return $ IntV pr₁ $ ClearZV $ trPrInt pr₁ i
  (AbsO    , [ IntV pr (ClearZV i) ]) → return $ NatV pr  $ ClearNV $ zabs i

  (PlusO , [ IntV pr₁ (ClearZV i₁), IntV pr₂ (ClearZV i₂) ]) | pr₁ ≡ pr₂ → return $ IntV pr₁ $ ClearZV $ trPrInt pr₁ $ i₁ + i₂
  (MinusO, [ IntV pr₁ (ClearZV i₁), IntV pr₂ (ClearZV i₂) ]) | pr₁ ≡ pr₂ → return $ IntV pr₁ $ ClearZV $ trPrInt pr₁ $ i₁ - i₂
  (TimesO, [ IntV pr₁ (ClearZV i₁), IntV pr₂ (ClearZV i₂) ]) | pr₁ ≡ pr₂ → return $ IntV pr₁ $ ClearZV $ trPrInt pr₁ $ i₁ × i₂
  (ExpO  , [ IntV pr₁ (ClearZV i₁), NatV pr₂ (ClearNV n₂) ]) | pr₁ ≡ pr₂ → return $ IntV pr₁ $ ClearZV $ trPrInt pr₁ $ i₁ ^^ n₂
  (DivO  , [ IntV pr₁ (ClearZV i₁), IntV pr₂ (ClearZV i₂) ]) | pr₁ ≡ pr₂ → return $ IntV pr₁ $ ClearZV $ trPrInt pr₁ $ if i₂ ≡ int 0 then i₁ else i₁ ⌿ i₂
  (ModO  , [ IntV pr₁ (ClearZV i₁), IntV pr₂ (ClearZV i₂) ]) | pr₁ ≡ pr₂ → return $ IntV pr₁ $ ClearZV $ trPrInt pr₁ $ if i₂ ≡ int 0 then i₁ else i₁ ÷ i₂
  (EqO   , [ IntV pr₁ (ClearZV i₁), IntV pr₂ (ClearZV i₂) ]) | pr₁ ≡ pr₂ → return $ BoolV    $ ClearBV $ i₁ ≡ i₂
  (LTO   , [ IntV pr₁ (ClearZV i₁), IntV pr₂ (ClearZV i₂) ]) | pr₁ ≡ pr₂ → return $ BoolV    $ ClearBV $ i₁ < i₂
  (LTEO  , [ IntV pr₁ (ClearZV i₁), IntV pr₂ (ClearZV i₂) ]) | pr₁ ≡ pr₂ → return $ BoolV    $ ClearBV $ i₁ ≤ i₂
  (GTO   , [ IntV pr₁ (ClearZV i₁), IntV pr₂ (ClearZV i₂) ]) | pr₁ ≡ pr₂ → return $ BoolV    $ ClearBV $ i₁ > i₂
  (GTEO  , [ IntV pr₁ (ClearZV i₁), IntV pr₂ (ClearZV i₂) ]) | pr₁ ≡ pr₂ → return $ BoolV    $ ClearBV $ i₁ ≥ i₂

  (CondO, [ BoolV (ClearBV b), IntV pr₁ (ClearZV i₁), IntV pr₂ (ClearZV i₂) ]) | pr₁ ≡ pr₂ → return $ IntV pr₁ $ ClearZV $ if b then i₁ else i₂

  -- Principals
  (EqO, [ PrinV ρv₁, PrinV ρv₂ ]) → return $ BoolV $ ClearBV $ ρv₁ ≡ ρv₂

  -- Principal Sets
  (PlusO, [ PrinSetV ρvs₁, PrinSetV ρvs₂ ]) → return $ PrinSetV $ PowPSV $ (elimPSV ρvs₁) ∪ (elimPSV ρvs₂)

  _ → todoCxt
