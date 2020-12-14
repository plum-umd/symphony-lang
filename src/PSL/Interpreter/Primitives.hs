module PSL.Interpreter.Primitives where

import UVMHS

import PSL.Interpreter.Types
import PSL.Interpreter.Truncating
import PSL.Interpreter.Pretty ()
import PSL.Syntax
import PSL.Interpreter.Json
import PSL.Interpreter.EMP as EMP

import AddToUVMHS

interpPrim ∷ (STACK) ⇒ Op → 𝐿 BaseValMPC → IM BaseValMPC
interpPrim o vs = case (o,tohs vs) of
  (OrO     ,[BoolMV b₁  ,BoolMV b₂  ])               → return $ BoolMV   $ b₁ ⩔ b₂
  (AndO    ,[BoolMV b₁  ,BoolMV b₂  ])               → return $ BoolMV   $ b₁ ⩓ b₂
  (NotO    ,[BoolMV b])                              → return $ BoolMV   $ not b
  (PlusO   ,[BoolMV b₁  ,BoolMV b₂  ])               → return $ BoolMV   $ b₁ ⩔ b₂
  (PlusO   ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→ return $ NatMV p₁ $ trPrNat p₁ $ n₁ + n₂
  (PlusO   ,[IntMV p₁ (IntSeqSh i₁),IntMV p₂ (IntSeqSh i₂)])         |p₁≡p₂→ return $ IntMV p₁ $ IntSeqSh $ trPrInt p₁ $ i₁ + i₂
  (PlusO   ,[IntMV p₁ (IntEMPSh i₁),IntMV p₂ (IntEMPSh i₂)])         |p₁≡p₂→ io (EMP.integerAdd i₁ i₂) >>= \ result →  return $ IntMV p₁ $ IntEMPSh result
  (PlusO   ,[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→ return $ FltMV p₁ $ f₁ + f₂
  (PlusO   ,[PrinMV ρ₁  ,PrinMV ρ₂  ])               → return $ PrinMV   $ ρ₁ ⊔ ρ₂
  (MinusO  ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→ return $ NatMV p₁ $ trPrNat p₁ $ buPrNat p₁ n₁ - n₂
  (MinusO  ,[IntMV p₁ (IntSeqSh i₁),IntMV p₂ (IntSeqSh i₂)])         |p₁≡p₂→ return $ IntMV p₁ $ IntSeqSh $ trPrInt p₁ $ i₁ - i₂
  (MinusO  ,[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→ return $ FltMV p₁ $ f₁ - f₂
  (TimesO  ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→ return $ NatMV p₁ $ trPrNat p₁ $ n₁ × n₂
  (TimesO  ,[IntMV p₁ (IntSeqSh i₁),IntMV p₂ (IntSeqSh i₂)])         |p₁≡p₂→ return $ IntMV p₁ $ IntSeqSh $ trPrInt p₁ $ i₁ × i₂
  (TimesO  ,[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→ return $ FltMV p₁ $ f₁ × f₂
  (ExpO    ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→ return $ NatMV p₁ $ trPrNat p₁ $ n₁ ^^ n₂
  (ExpO    ,[IntMV p₁ (IntSeqSh i₁),NatMV p₂ n₂])         |p₁≡p₂→ return $ IntMV p₁ $ IntSeqSh $ trPrInt p₁ $ i₁ ^^ n₂
  (ExpO    ,[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→ return $ FltMV p₁ $ f₁ ^ f₂
  (DivO    ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→ return $ NatMV p₁ $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ⌿ n₂
  (DivO    ,[IntMV p₁ (IntSeqSh i₁),IntMV p₂ (IntSeqSh i₂)])         |p₁≡p₂→ return $ IntMV p₁ $ IntSeqSh $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ⌿ i₂
  (DivO    ,[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→ return $ FltMV p₁ $              if f₂ ≡ 0.0   then f₁ else f₁ / f₂
  (ModO    ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→ return $ NatMV p₁ $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ÷ n₂
  (ModO    ,[IntMV p₁ (IntSeqSh i₁),IntMV p₂ (IntSeqSh i₂)])         |p₁≡p₂→ return $ IntMV p₁ $ IntSeqSh $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ÷ i₂
  (EqO     ,[BoolMV b₁  ,BoolMV b₂  ])               → return $ BoolMV   $ b₁ ≡ b₂
  (EqO     ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→ return $ BoolMV   $ n₁ ≡ n₂
  (EqO     ,[IntMV p₁ (IntSeqSh i₁),IntMV p₂ (IntSeqSh i₂)])         |p₁≡p₂→ return $ BoolMV   $ i₁ ≡ i₂
  (EqO     ,[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→ return $ BoolMV   $ f₁ ≡ f₂
  (EqO     ,[PrinMV ρev₁,PrinMV ρev₂])               → return $ BoolMV   $ ρev₁ ≡ ρev₂
  (LTO     ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→ return $ BoolMV   $ n₁ < n₂
  (LTO     ,[IntMV p₁ (IntSeqSh i₁),IntMV p₂ (IntSeqSh i₂)])         |p₁≡p₂→ return $ BoolMV   $ i₁ < i₂
  (LTO     ,[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→ return $ BoolMV   $ f₁ < f₂
  (GTO     ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→ return $ BoolMV   $ n₁ > n₂
  (GTO     ,[IntMV p₁ (IntSeqSh i₁),IntMV p₂ (IntSeqSh i₂)])         |p₁≡p₂→ return $ BoolMV   $ i₁ > i₂
  (GTO     ,[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→ return $ BoolMV   $ f₁ > f₂
  (LTEO    ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→ return $ BoolMV   $ n₁ ≤ n₂
  (LTEO    ,[IntMV p₁ (IntSeqSh i₁),IntMV p₂ (IntSeqSh i₂)])         |p₁≡p₂→ return $ BoolMV   $ i₁ ≤ i₂
  (LTEO    ,[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→ return $ BoolMV   $ f₁ ≤ f₂
  (GTEO    ,[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→ return $ BoolMV   $ n₁ ≥ n₂
  (GTEO    ,[IntMV p₁ (IntSeqSh i₁),IntMV p₂ (IntSeqSh i₂)])         |p₁≡p₂→ return $ BoolMV   $ i₁ ≥ i₂
  (GTEO    ,[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→ return $ BoolMV   $ f₁ ≥ f₂
  (CondO   ,[BoolMV b,BoolMV b₁  ,BoolMV b₂  ])      → return $ BoolMV   $ if b then b₁ else b₂
  (CondO   ,[BoolMV b,NatMV p₁ n₁,NatMV p₂ n₂])|p₁≡p₂→ return $ NatMV p₁ $ if b then n₁ else n₂
  (CondO   ,[BoolMV b,IntMV p₁ (IntSeqSh i₁),IntMV p₂ (IntSeqSh i₂)])|p₁≡p₂→ return $ IntMV p₁ $ IntSeqSh $ if b then i₁ else i₂
  (CondO   ,[BoolMV b,FltMV p₁ f₁,FltMV p₂ f₂])|p₁≡p₂→ return $ FltMV p₁ $ if b then f₁ else f₂
  (CondO   ,[BoolMV b,PrinMV p₁  ,PrinMV p₂  ])      → return $ PrinMV   $ if b then p₁ else p₂
  (AbsO    ,[IntMV p (IntSeqSh i)])                             → return $ NatMV p  $ zabs i
  (LogO    ,[FltMV p f])                             → return $ FltMV p  $ logBase 2.0 f
  (SqrtO   ,[FltMV p f])                             → return $ FltMV p  $ root f
  (NatO p₁ ,[NatMV p₂ n])                            → return $ NatMV p₁ $ trPrNat p₁ n
  (NatO p₁ ,[IntMV p₂ (IntSeqSh i)])                            → return $ NatMV p₁ $ trPrNat p₁ $ natΩ i
  (IntO p₁ ,[IntMV p₂ (IntSeqSh i)])                            → return $ IntMV p₁ $ IntSeqSh $ trPrInt p₁ i
  (IntO p₁ ,[NatMV p₂ n])                            → return $ IntMV p₁ $ IntSeqSh $ trPrInt p₁ $ int n
  (FltO p₁ ,[NatMV p₂ n])                            → return $ FltMV p₁ $ dbl n
  (FltO p₁ ,[IntMV p₂ (IntSeqSh i)])                            → return $ FltMV p₁ $ dbl i
  (FltO p₁ ,[FltMV p₂ d])                            → return $ FltMV p₁ $ d
  (CeilO p₁,[FltMV p₂ f])                            → return $ IntMV p₁ $ IntSeqSh $ ceiling f
  _ → throwIErrorCxt NotImplementedIError "interpPrim" $ frhs
    [ ("o",pretty o)
    , ("vs",pretty vs)
    ]

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
  LogO → "LOG₂"
  NatO _p → "NAT"
  IntO _p → "INT"
  FltO _p → "FLT"
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
  Shared φ _ → multDepth φ op
