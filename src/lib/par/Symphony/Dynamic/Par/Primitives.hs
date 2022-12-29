module Symphony.Dynamic.Par.Primitives where

import Symphony.Prelude

import Symphony.Lang.Syntax

import Symphony.Dynamic.Par.Types
import Symphony.Dynamic.Par.Truncating
import Symphony.Dynamic.Par.Error

import Symphony.Dynamic.Par.GMW

import qualified Data.Bits as BITS

metaBaseVal ∷ BaseVal → 𝑂 (Prot ∧ 𝑃 PrinVal)
metaBaseVal bv = case bv of
  BoolV  (ClearBV _) → None
  NatV _ (ClearNV _) → None
  IntV _ (ClearZV _) → None
  BoolV  (EncBV ρvs (RepB _)) → Some $ RepP :* ρvs
  NatV _ (EncNV ρvs (RepN _)) → Some $ RepP :* ρvs
  IntV _ (EncZV ρvs (RepZ _)) → Some $ RepP :* ρvs
  BoolV  (EncBV ρvs (GmwB _)) → Some $ GmwP :* ρvs
  NatV _ (EncNV ρvs (GmwN _)) → Some $ GmwP :* ρvs
  IntV _ (EncZV ρvs (GmwZ _)) → Some $ GmwP :* ρvs
  _ → None

metaComb ∷ 𝑂 (Prot ∧ 𝑃 PrinVal) → 𝑂 (Prot ∧ 𝑃 PrinVal) → IM Val (𝑂 (Prot ∧ 𝑃 PrinVal))
metaComb meta1 meta2 = case (meta1, meta2) of
  (None   , None   ) → return None
  (None   , _      ) → return meta2
  (_      , None   ) → return meta1
  (Some m₁, Some m₂) → do
    guardErr (m₁ ≡ m₂) $
      throwIErrorCxt TypeIError "metaComb: m₁ ≢ m₂" $ frhs
      [ ("m₁", pretty m₁)
      , ("m₂", pretty m₂)
      ]
    return meta1

metaBaseVals ∷ 𝐿 BaseVal → IM Val (𝑂 (Prot ∧ 𝑃 PrinVal))
metaBaseVals bvs = mfold None metaComb $ map metaBaseVal bvs

embedBaseVal ∷ 𝑂 (Prot ∧ 𝑃 PrinVal) → BaseVal → IM Val BaseVal
embedBaseVal meta bv = case meta of
  None            → return bv
  Some (φ :* ρvs) → case φ of
    RepP → case bv of
      BoolV   (ClearBV b) → BoolV   ^$ EncBV ρvs ^$ return $ RepB b
      NatV pr (ClearNV n) → NatV pr ^$ EncNV ρvs ^$ return $ RepN n
      IntV pr (ClearZV z) → IntV pr ^$ EncZV ρvs ^$ return $ RepZ z
      _ → return bv
    GmwP → do
      gmw ← getOrMkGmw ρvs
      case bv of
        BoolV   (ClearBV b) → BoolV   ^$ EncBV ρvs ^$ GmwB ^$ gmwBoolConstant gmw b
        NatV pr (ClearNV n) → NatV pr ^$ EncNV ρvs ^$ GmwN ^$ gmwNatConstant gmw pr n
        IntV pr (ClearZV z) → IntV pr ^$ EncZV ρvs ^$ GmwZ ^$ gmwIntConstant gmw pr z
        _                   → return bv

embedBaseVals ∷ 𝐿 BaseVal → IM Val (𝐿 BaseVal)
embedBaseVals bvs = do
  meta ← metaBaseVals bvs
  mapM (embedBaseVal meta) bvs

primBaseVal ∷ Op → 𝐿 BaseVal → IM Val BaseVal
primBaseVal op bvs = do
  bvs ← embedBaseVals bvs
  case (op, tohs bvs) of
    -----------
    -- Clear --
    -----------

    --- Unit

    (CondO, [ BoolV _, BulV, BulV ]) → return BulV

    --- Booleans

    (NotO, [ BoolV (ClearBV b) ]) → return $ BoolV $ ClearBV $ not b

    (AndO, [ BoolV (ClearBV b₁), BoolV (ClearBV b₂) ]) → return $ BoolV $ ClearBV $ b₁ ⩓ b₂
    (OrO , [ BoolV (ClearBV b₁), BoolV (ClearBV b₂) ]) → return $ BoolV $ ClearBV $ b₁ ⩔ b₂
    (EqO , [ BoolV (ClearBV b₁), BoolV (ClearBV b₂) ]) → return $ BoolV $ ClearBV $ b₁ ≡ b₂

    (CondO, [ BoolV (ClearBV b), BoolV (ClearBV b₁), BoolV (ClearBV b₂) ]) → return $ BoolV $ ClearBV $ if b then b₁ else b₂

    --- Naturals

    (NatO pr₁, [ NatV _ (ClearNV n) ]) → return $ NatV pr₁ $ ClearNV $ trPrNat pr₁ n
    (IntO pr₁, [ NatV _ (ClearNV n) ]) → return $ IntV pr₁ $ ClearZV $ trPrInt pr₁ $ int n
    (BoolO   , [ NatV _ (ClearNV n) ]) → return $ BoolV    $ ClearBV $ n ≢ 0

    (XorO  , [ NatV pr₁ (ClearNV n₁), NatV pr₂ (ClearNV n₂) ]) | pr₁ ≡ pr₂ → return $ NatV pr₁ $ ClearNV $ trPrNat pr₁ $ n₁ `BITS.xor` n₂
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

    (CondO, [ BoolV (ClearBV b)         , NatV pr₁ (ClearNV n₁)       , NatV pr₂ (ClearNV n₂)        ]) | pr₁ ≡ pr₂ → return $ NatV pr₁ $ ClearNV $ if b then n₁ else n₂

    --- Integers

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

    --- Principals

    (EqO, [ PrinV ρv₁, PrinV ρv₂ ]) → return $ BoolV $ ClearBV $ ρv₁ ≡ ρv₂

    --- Principal Sets

    (PlusO, [ PrinSetV ρvs₁, PrinSetV ρvs₂ ]) → return $ PrinSetV $ PowPSV $ (elimPSV ρvs₁) ∪ (elimPSV ρvs₂)

    ----------------
    -- Replicated --
    ----------------

    --- Booleans

    (OrO, [ BoolV (EncBV ρvs (RepB b₁)), BoolV (EncBV _ (RepB b₂)) ]) → BoolV ^$ EncBV ρvs ^$ RepB ^$ return $ b₁ ⩔ b₂

    (CondO, [ BoolV (EncBV ρvs (RepB b₁)), BoolV (EncBV _ (RepB b₂)), BoolV (EncBV _ (RepB b₃)) ]) → BoolV ^$ EncBV ρvs ^$ RepB ^$ return $ if b₁ then b₂ else b₃

    --- Naturals

    (PlusO , [ NatV pr₁ (EncNV ρvs (RepN n₁)), NatV pr₂ (EncNV _ (RepN n₂)) ]) | pr₁ ≡ pr₂ → NatV pr₁ ^$ EncNV ρvs ^$ RepN ^$ return $ trPrNat pr₁ $ n₁ + n₂
    (TimesO, [ NatV pr₁ (EncNV ρvs (RepN n₁)), NatV pr₂ (EncNV _ (RepN n₂)) ]) | pr₁ ≡ pr₂ → NatV pr₁ ^$ EncNV ρvs ^$ RepN ^$ return $ trPrNat pr₁ $ n₁ × n₂

    (EqO   , [ NatV pr₁ (EncNV ρvs (RepN n₁)), NatV pr₂ (EncNV _ (RepN n₂)) ]) | pr₁ ≡ pr₂ → BoolV ^$ EncBV ρvs ^$ RepB ^$ return $ n₁ ≡ n₂
    (LTEO  , [ NatV pr₁ (EncNV ρvs (RepN n₁)), NatV pr₂ (EncNV _ (RepN n₂)) ]) | pr₁ ≡ pr₂ → BoolV ^$ EncBV ρvs ^$ RepB ^$ return $ n₁ ≤ n₂

    (CondO, [ BoolV (EncBV ρvs (RepB b)), NatV pr₁ (EncNV _ (RepN n₁)), NatV pr₂ (EncNV _ (RepN n₂)) ]) | pr₁ ≡ pr₂ → NatV pr₁ ^$ EncNV ρvs ^$ RepN ^$ return $ if b then n₁ else n₂

    --- Integers

    (PlusO , [ IntV pr₁ (EncZV ρvs (RepZ z₁)), IntV pr₂ (EncZV _ (RepZ z₂)) ]) | pr₁ ≡ pr₂ → IntV pr₁ ^$ EncZV ρvs ^$ RepZ ^$ return $ trPrInt pr₁ $ z₁ + z₂
    (MinusO, [ IntV pr₁ (EncZV ρvs (RepZ z₁)), IntV pr₂ (EncZV _ (RepZ z₂)) ]) | pr₁ ≡ pr₂ → IntV pr₁ ^$ EncZV ρvs ^$ RepZ ^$ return $ trPrInt pr₁ $ z₁ - z₂
    (TimesO, [ IntV pr₁ (EncZV ρvs (RepZ z₁)), IntV pr₂ (EncZV _ (RepZ z₂)) ]) | pr₁ ≡ pr₂ → IntV pr₁ ^$ EncZV ρvs ^$ RepZ ^$ return $ trPrInt pr₁ $ z₁ × z₂
    (DivO  , [ IntV pr₁ (EncZV ρvs (RepZ z₁)), IntV pr₂ (EncZV _ (RepZ z₂)) ]) | pr₁ ≡ pr₂ → IntV pr₁ ^$ EncZV ρvs ^$ RepZ ^$ return $ trPrInt pr₁ $ if z₂ ≡ int 0 then z₁ else z₁ ⌿ z₂
    (ModO  , [ IntV pr₁ (EncZV ρvs (RepZ z₁)), IntV pr₂ (EncZV _ (RepZ z₂)) ]) | pr₁ ≡ pr₂ → IntV pr₁ ^$ EncZV ρvs ^$ RepZ ^$ return $ trPrInt pr₁ $ if z₂ ≡ int 0 then z₁ else z₁ ÷ z₂

    (EqO , [ IntV pr₁ (EncZV ρvs (RepZ z₁)), IntV pr₂ (EncZV _ (RepZ z₂)) ]) | pr₁ ≡ pr₂ → BoolV ^$ EncBV ρvs ^$ RepB ^$ return $ z₁ ≡ z₂
    (LTO , [ IntV pr₁ (EncZV ρvs (RepZ z₁)), IntV pr₂ (EncZV _ (RepZ z₂)) ]) | pr₁ ≡ pr₂ → BoolV ^$ EncBV ρvs ^$ RepB ^$ return $ z₁ < z₂
    (LTEO, [ IntV pr₁ (EncZV ρvs (RepZ z₁)), IntV pr₂ (EncZV _ (RepZ z₂)) ]) | pr₁ ≡ pr₂ → BoolV ^$ EncBV ρvs ^$ RepB ^$ return $ z₁ ≤ z₂

    (CondO, [ BoolV (EncBV ρvs (RepB b)), IntV pr₁ (EncZV _ (RepZ z₁)), IntV pr₂ (EncZV _ (RepZ z₂)) ]) | pr₁ ≡ pr₂ → IntV pr₁ ^$ EncZV ρvs ^$ RepZ ^$ return $ if b then z₁ else z₂

    ---------
    -- GMW --
    ---------

    --- Booleans

    (OrO, [ BoolV (EncBV ρvs (GmwB b₁)), BoolV (EncBV _ (GmwB b₂)) ]) → BoolV ^$ EncBV ρvs ^$ GmwB ^$ do { gmw ← getOrMkGmw ρvs ; gmwBoolOr gmw b₁ b₂ }

    (CondO, [ BoolV (EncBV ρvs (GmwB b₁)), BoolV (EncBV _ (GmwB b₂)), BoolV (EncBV _ (GmwB b₃)) ]) → BoolV ^$ EncBV ρvs ^$ GmwB ^$ do { gmw ← getOrMkGmw ρvs ; gmwBoolMux gmw b₁ b₂ b₃ }

    --- Naturals

    (PlusO , [ NatV pr₁ (EncNV ρvs (GmwN n₁)), NatV pr₂ (EncNV _ (GmwN n₂)) ]) | pr₁ ≡ pr₂ → NatV pr₁ ^$ EncNV ρvs ^$ GmwN ^$ do { gmw ← getOrMkGmw ρvs ; gmwNatAdd gmw n₁ n₂ }
    (TimesO, [ NatV pr₁ (EncNV ρvs (GmwN n₁)), NatV pr₂ (EncNV _ (GmwN n₂)) ]) | pr₁ ≡ pr₂ → NatV pr₁ ^$ EncNV ρvs ^$ GmwN ^$ do { gmw ← getOrMkGmw ρvs ; gmwNatMul gmw n₁ n₂ }

    (EqO   , [ NatV pr₁ (EncNV ρvs (GmwN n₁)), NatV pr₂ (EncNV _ (GmwN n₂)) ]) | pr₁ ≡ pr₂ → BoolV ^$ EncBV ρvs ^$ GmwB ^$ do { gmw ← getOrMkGmw ρvs ; gmwNatEq gmw n₁ n₂ }
    (LTEO  , [ NatV pr₁ (EncNV ρvs (GmwN n₁)), NatV pr₂ (EncNV _ (GmwN n₂)) ]) | pr₁ ≡ pr₂ → BoolV ^$ EncBV ρvs ^$ GmwB ^$ do { gmw ← getOrMkGmw ρvs ; gmwNatLte gmw n₁ n₂ }

    (CondO, [ BoolV (EncBV ρvs (GmwB b)), NatV pr₁ (EncNV _ (GmwN n₁)), NatV pr₂ (EncNV _ (GmwN n₂)) ]) | pr₁ ≡ pr₂ →
      NatV pr₁ ^$ EncNV ρvs ^$ GmwN ^$ do { gmw ← getOrMkGmw ρvs ; gmwNatMux gmw b n₁ n₂ }

    --- Integers

    (PlusO , [ IntV pr₁ (EncZV ρvs (GmwZ z₁)), IntV pr₂ (EncZV _ (GmwZ z₂)) ]) | pr₁ ≡ pr₂ → IntV pr₁ ^$ EncZV ρvs ^$ GmwZ ^$ do { gmw ← getOrMkGmw ρvs ; gmwIntAdd gmw z₁ z₂ }
    (MinusO, [ IntV pr₁ (EncZV ρvs (GmwZ z₁)), IntV pr₂ (EncZV _ (GmwZ z₂)) ]) | pr₁ ≡ pr₂ → IntV pr₁ ^$ EncZV ρvs ^$ GmwZ ^$ do { gmw ← getOrMkGmw ρvs ; gmwIntSub gmw z₁ z₂ }
    (TimesO, [ IntV pr₁ (EncZV ρvs (GmwZ z₁)), IntV pr₂ (EncZV _ (GmwZ z₂)) ]) | pr₁ ≡ pr₂ → IntV pr₁ ^$ EncZV ρvs ^$ GmwZ ^$ do { gmw ← getOrMkGmw ρvs ; gmwIntMul gmw z₁ z₂ }
    (DivO  , [ IntV pr₁ (EncZV ρvs (GmwZ z₁)), IntV pr₂ (EncZV _ (GmwZ z₂)) ]) | pr₁ ≡ pr₂ → IntV pr₁ ^$ EncZV ρvs ^$ GmwZ ^$ do { gmw ← getOrMkGmw ρvs ; gmwIntDiv gmw z₁ z₂ }
    (ModO  , [ IntV pr₁ (EncZV ρvs (GmwZ z₁)), IntV pr₂ (EncZV _ (GmwZ z₂)) ]) | pr₁ ≡ pr₂ → IntV pr₁ ^$ EncZV ρvs ^$ GmwZ ^$ do { gmw ← getOrMkGmw ρvs ; gmwIntMod gmw z₁ z₂ }

    (EqO , [ IntV pr₁ (EncZV ρvs (GmwZ z₁)), IntV pr₂ (EncZV _ (GmwZ z₂)) ]) | pr₁ ≡ pr₂ → BoolV ^$ EncBV ρvs ^$ GmwB ^$ do { gmw ← getOrMkGmw ρvs ; gmwIntEq gmw z₁ z₂ }
    (LTO , [ IntV pr₁ (EncZV ρvs (GmwZ z₁)), IntV pr₂ (EncZV _ (GmwZ z₂)) ]) | pr₁ ≡ pr₂ → BoolV ^$ EncBV ρvs ^$ GmwB ^$ do { gmw ← getOrMkGmw ρvs ; gmwIntLt gmw z₁ z₂ }
    (LTEO, [ IntV pr₁ (EncZV ρvs (GmwZ z₁)), IntV pr₂ (EncZV _ (GmwZ z₂)) ]) | pr₁ ≡ pr₂ → BoolV ^$ EncBV ρvs ^$ GmwB ^$ do { gmw ← getOrMkGmw ρvs ; gmwIntLte gmw z₁ z₂ }

    (CondO, [ BoolV (EncBV ρvs (GmwB b)), IntV pr₁ (EncZV _ (GmwZ z₁)), IntV pr₂ (EncZV _ (GmwZ z₂)) ]) | pr₁ ≡ pr₂ →
      IntV pr₁ ^$ EncZV ρvs ^$ GmwZ ^$ do { gmw ← getOrMkGmw ρvs ; gmwIntMux gmw b z₁ z₂ }

    _ → do
      pptraceM (op, bvs)
      todoCxt
