module PSL.Interpreter.Primitives where

import UVMHS

import PSL.Interpreter.Types
import PSL.Interpreter.Truncating
import PSL.Interpreter.Pretty ()
import PSL.Syntax
import PSL.Interpreter.Json

valWithType ∷ Val → Val ∧ 𝕊
valWithType v = v :* getType v

tnat ∷ IPrecision → 𝕊
tnat p = "nat"⧺iprecisionSuffix p

tint ∷ IPrecision → 𝕊
tint p = "int"⧺iprecisionSuffix p

tflt ∷ FPrecision → 𝕊
tflt p = "flt"⧺fprecisionSuffix p

tboo ∷ 𝕊
tboo = "bool"

tprn ∷ 𝕊
tprn = "prin"

interpPrim ∷ (STACK) ⇒ Op → 𝐿 BaseValMPC → IM (𝕊 ∧ 𝕊 ∧ BaseValMPC)
interpPrim o vs = case (o,tohs vs) of
  (OrO     ,[BoolMV b₁  ,BoolMV b₂  ])               →r (tboo   ) (null   ) $ BoolMV   $ b₁ ⩔ b₂
  (AndO    ,[BoolMV b₁  ,BoolMV b₂  ])               →r (tboo   ) (null   ) $ BoolMV   $ b₁ ⩓ b₂
  (NotO    ,[BoolMV b])                              →r (tboo   ) (null   ) $ BoolMV   $ not b  
  (PlusO   ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→r (tnat p₁) (null   ) $ NatMV p₁ $ trPrNat p₁ $ n₁ + n₂
  (PlusO   ,[IntMV p₁ i₁,IntMV p₂ i₂])         |p₁≡p₂→r (tint p₁) (null   ) $ IntMV p₁ $ trPrInt p₁ $ i₁ + i₂
  (PlusO   ,[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→r (tflt p₁) (null   ) $ FltMV p₁ $ f₁ + f₂
  (MinusO  ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→r (tnat p₁) (null   ) $ NatMV p₁ $ trPrNat p₁ $ buPrNat p₁ n₁ - n₂
  (MinusO  ,[IntMV p₁ i₁,IntMV p₂ i₂])         |p₁≡p₂→r (tint p₁) (null   ) $ IntMV p₁ $ trPrInt p₁ $ i₁ - i₂
  (MinusO  ,[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→r (tflt p₁) (null   ) $ FltMV p₁ $ f₁ - f₂
  (TimesO  ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→r (tnat p₁) (null   ) $ NatMV p₁ $ trPrNat p₁ $ n₁ × n₂
  (TimesO  ,[IntMV p₁ i₁,IntMV p₂ i₂])         |p₁≡p₂→r (tint p₁) (null   ) $ IntMV p₁ $ trPrInt p₁ $ i₁ × i₂
  (TimesO  ,[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→r (tflt p₁) (null   ) $ FltMV p₁ $ f₁ × f₂
  (ExpO    ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→r (tnat p₁) (null   ) $ NatMV p₁ $ trPrNat p₁ $ n₁ ^^ n₂
  (ExpO    ,[IntMV p₁ i₁,NatMV p₂ n₂])         |p₁≡p₂→r (tint p₁) (null   ) $ IntMV p₁ $ trPrInt p₁ $ i₁ ^^ n₂
  (ExpO    ,[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→r (tflt p₁) (null   ) $ FltMV p₁ $ f₁ ^ f₂
  (DivO    ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→r (tnat p₁) (null   ) $ NatMV p₁ $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ⌿ n₂
  (DivO    ,[IntMV p₁ i₁,IntMV p₂ i₂])         |p₁≡p₂→r (tint p₁) (null   ) $ IntMV p₁ $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ⌿ i₂
  (DivO    ,[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→r (tflt p₁) (null   ) $ FltMV p₁ $              if f₂ ≡ 0.0   then f₁ else f₁ / f₂
  (ModO    ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→r (tnat p₁) (null   ) $ NatMV p₁ $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ÷ n₂
  (ModO    ,[IntMV p₁ i₁,IntMV p₂ i₂])         |p₁≡p₂→r (tint p₁) (null   ) $ IntMV p₁ $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ÷ i₂
  (EqO     ,[BoolMV b₁  ,BoolMV b₂  ])               →r (tboo   ) (null   ) $ BoolMV   $ b₁ ≡ b₂
  (EqO     ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→r (tnat p₁) (null   ) $ BoolMV   $ n₁ ≡ n₂
  (EqO     ,[IntMV p₁ i₁,IntMV p₂ i₂])         |p₁≡p₂→r (tint p₁) (null   ) $ BoolMV   $ i₁ ≡ i₂
  (EqO     ,[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→r (tflt p₁) (null   ) $ BoolMV   $ f₁ ≡ f₂
  (EqO     ,[PrinMV ρev₁,PrinMV ρev₂])               →r (tprn   ) (null   ) $ BoolMV   $ ρev₁ ≡ ρev₂
  (LTO     ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→r (tnat p₁) (null   ) $ BoolMV   $ n₁ < n₂
  (LTO     ,[IntMV p₁ i₁,IntMV p₂ i₂])         |p₁≡p₂→r (tint p₁) (null   ) $ BoolMV   $ i₁ < i₂
  (LTO     ,[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→r (tflt p₁) (null   ) $ BoolMV   $ f₁ < f₂
  (GTO     ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→r (tnat p₁) (null   ) $ BoolMV   $ n₁ > n₂
  (GTO     ,[IntMV p₁ i₁,IntMV p₂ i₂])         |p₁≡p₂→r (tint p₁) (null   ) $ BoolMV   $ i₁ > i₂
  (GTO     ,[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→r (tflt p₁) (null   ) $ BoolMV   $ f₁ > f₂
  (LTEO    ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→r (tnat p₁) (null   ) $ BoolMV   $ n₁ ≤ n₂
  (LTEO    ,[IntMV p₁ i₁,IntMV p₂ i₂])         |p₁≡p₂→r (tint p₁) (null   ) $ BoolMV   $ i₁ ≤ i₂
  (LTEO    ,[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→r (tflt p₁) (null   ) $ BoolMV   $ f₁ ≤ f₂
  (GTEO    ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→r (tnat p₁) (null   ) $ BoolMV   $ n₁ ≥ n₂
  (GTEO    ,[IntMV p₁ i₁,IntMV p₂ i₂])         |p₁≡p₂→r (tint p₁) (null   ) $ BoolMV   $ i₁ ≥ i₂
  (GTEO    ,[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→r (tflt p₁) (null   ) $ BoolMV   $ f₁ ≥ f₂
  (CondO   ,[BoolMV b,BoolMV b₁  ,BoolMV b₂  ])      →r (tboo   ) (null   ) $ BoolMV   $ if b then b₁ else b₂
  (CondO   ,[BoolMV b,NatMV p₁ n₁,NatMV p₂ n₂])|p₁≡p₂→r (tnat p₁) (null   ) $ NatMV p₁ $ if b then n₁ else n₂
  (CondO   ,[BoolMV b,IntMV p₁ i₁,IntMV p₂ i₂])|p₁≡p₂→r (tint p₁) (null   ) $ IntMV p₁ $ if b then i₁ else i₂
  (CondO   ,[BoolMV b,FltMV p₁ f₁,FltMV p₂ f₂])|p₁≡p₂→r (tflt p₁) (null   ) $ FltMV p₁ $ if b then f₁ else f₂
  (CondO   ,[BoolMV b,PrinMV p₁  ,PrinMV p₂  ])      →r (tprn   ) (null   ) $ PrinMV   $ if b then p₁ else p₂
  (AbsO    ,[IntMV p i])                             →r (tint p ) (null   ) $ NatMV p  $ zabs i
  (SqrtO   ,[FltMV p f])                             →r (tflt p ) (null   ) $ FltMV p  $ root f
  (NatO p₁ ,[NatMV p₂ n])                            →r (tnat p₂) (tnat p₁) $ NatMV p₁ $ trPrNat p₁ n
  (NatO p₁ ,[IntMV p₂ i])                            →r (tnat p₂) (tint p₁) $ NatMV p₁ $ trPrNat p₁ $ natΩ i
  (IntO p₁ ,[IntMV p₂ i])                            →r (tint p₂) (tint p₁) $ IntMV p₁ $ trPrInt p₁ i
  (IntO p₁ ,[NatMV p₂ n])                            →r (tnat p₂) (tint p₁) $ IntMV p₁ $ trPrInt p₁ $ int n
  (FltO p₁ ,[NatMV p₂ n])                            →r (tnat p₂) (tflt p₁) $ FltMV p₁ $ dbl n
  (FltO p₁ ,[IntMV p₂ i])                            →r (tint p₂) (tflt p₁) $ FltMV p₁ $ dbl i
  (FltO p₁ ,[FltMV p₂ d])                            →r (tflt p₂) (tflt p₁) $ FltMV p₁ $ d
  (CeilO p₁,[FltMV p₂ f])                            →r (tflt p₂) (tint p₁) $ IntMV p₁ $ ceiling f
  _ → throwIErrorCxt NotImplementedIError "interpPrim" $ frhs
    [ ("o",pretty o)
    , ("vs",pretty vs)
    ]
  where
    r s₁ s₂ v = return $ s₁ :* s₂ :* v

opName ∷ Op → 𝕊
opName = \case
  OrO → "OR"
  AndO → "AND"
  NotO → "NOT"
  PlusO → "PLUS"
  MinusO → "MINUS"
  TimesO → "TIMES"
  ExpO → "EXP"
  DivO → "DIV"
  ModO  → "MOD"
  EqO → "EQ"
  LTO → "LT"
  GTO → "GT"
  LTEO → "LTE"
  GTEO → "GTE"
  CondO → "COND"
  AbsO → "ABS"
  SqrtO → "SQRT"
  NatO _p → "TO_NAT" -- change to "NAT" later
  IntO _p → "TO_INT" -- change to "INT" later
  FltO _p → "TO_FLT" -- change to "FLT" later
  CeilO _p → "CEIL"


multDepth ∷ Prot → Op → ℕ
multDepth p o = case (p, o) of
  (_, TimesO) → 1
  (_, GTO) -> 1
  (_, LTO) -> 1
  (_, EqO) -> 1
  (_, GTEO) -> 1
  (_, LTEO) -> 1
  _ → 0 -- To be updated

multDepthShareInfo ∷ Op → ShareInfo → ℕ
multDepthShareInfo op = \case
  NotShared → zero
  Shared _ φ _ → multDepth φ op

