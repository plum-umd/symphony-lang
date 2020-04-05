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

multDepthShareInfo ∷ 𝕊 → ShareInfo → ℕ
multDepthShareInfo op = \case
  NotShared → zero
  Shared φ _ → multDepth φ op

multDepth ∷ Prot → 𝕊 → ℕ
multDepth p o = case (p, o) of
  (_, "TIMES") → 1
  (_, "GT") -> 1
  (_, "LT") -> 1
  (_, "EQ") -> 1
  (_, "GTE") -> 1
  (_, "LTE") -> 1
  _ → 0 -- To be updated

interpPrim ∷ (STACK) ⇒ 𝕊 → 𝐿 BaseValMPC → IM (𝕊 ∧ BaseValMPC)
interpPrim o vs = case (o,vs) of
  ("OR"   ,tohs→[BoolMV b₁  ,BoolMV b₂  ])               →rtboo    $ BoolMV         $ b₁ ⩔ b₂
  ("AND"  ,tohs→[BoolMV b₁  ,BoolMV b₂  ])               →rtboo    $ BoolMV         $ b₁ ⩓ b₂
  ("NOT"  ,tohs→[BoolMV b])                              →rtboo    $ BoolMV         $ not b  
  ("PLUS" ,tohs→[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→rtnat p₁ $ NatMV p₁       $ trPrNat p₁ $ n₁ + n₂
  ("PLUS" ,tohs→[IntMV p₁ i₁,IntMV p₂ i₂])         |p₁≡p₂→rtint p₁ $ IntMV p₁       $ trPrInt p₁ $ i₁ + i₂
  ("PLUS" ,tohs→[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→rtflt p₁ $ FltMV p₁       $ f₁ + f₂
  ("MINUS",tohs→[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→rtnat p₁ $ NatMV p₁       $ trPrNat p₁ $ buPrNat p₁ n₁ - n₂
  ("MINUS",tohs→[IntMV p₁ i₁,IntMV p₂ i₂])         |p₁≡p₂→rtint p₁ $ IntMV p₁       $ trPrInt p₁ $ i₁ - i₂
  ("MINUS",tohs→[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→rtflt p₁ $ FltMV p₁       $ f₁ - f₂
  ("TIMES",tohs→[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→rtnat p₁ $ NatMV p₁       $ trPrNat p₁ $ n₁ × n₂
  ("TIMES",tohs→[IntMV p₁ i₁,IntMV p₂ i₂])         |p₁≡p₂→rtint p₁ $ IntMV p₁       $ trPrInt p₁ $ i₁ × i₂
  ("TIMES",tohs→[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→rtflt p₁ $ FltMV p₁       $ f₁ × f₂
  ("EXP"  ,tohs→[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→rtnat p₁ $ NatMV p₁       $ trPrNat p₁ $ n₁ ^^ n₂
  ("EXP"  ,tohs→[IntMV p₁ i₁,NatMV p₂ n₂])         |p₁≡p₂→rtint p₁ $ IntMV p₁       $ trPrInt p₁ $ i₁ ^^ n₂
  ("EXP"  ,tohs→[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→rtflt p₁ $ FltMV p₁       $ f₁ ^ f₂
  ("DIV"  ,tohs→[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→rtnat p₁ $ NatMV p₁       $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ⌿ n₂
  ("DIV"  ,tohs→[IntMV p₁ i₁,IntMV p₂ i₂])         |p₁≡p₂→rtint p₁ $ IntMV p₁       $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ⌿ i₂
  ("DIV"  ,tohs→[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→rtflt p₁ $ FltMV p₁       $              if f₂ ≡ 0.0   then f₁ else f₁ / f₂
  ("MOD"  ,tohs→[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→rtnat p₁ $ NatMV p₁       $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ÷ n₂
  ("MOD"  ,tohs→[IntMV p₁ i₁,IntMV p₂ i₂])         |p₁≡p₂→rtint p₁ $ IntMV p₁       $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ÷ i₂
  ("EQ"   ,tohs→[BoolMV b₁  ,BoolMV b₂  ])               →rtboo    $ BoolMV         $ b₁ ≡ b₂
  ("EQ"   ,tohs→[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→rtnat p₁ $ BoolMV         $ n₁ ≡ n₂
  ("EQ"   ,tohs→[IntMV p₁ i₁,IntMV p₂ i₂])         |p₁≡p₂→rtint p₁ $ BoolMV         $ i₁ ≡ i₂
  ("EQ"   ,tohs→[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→rtflt p₁ $ BoolMV         $ f₁ ≡ f₂
  ("EQ"   ,tohs→[PrinMV ρev₁,PrinMV ρev₂])               →rtprn    $ BoolMV         $ ρev₁ ≡ ρev₂
  ("LT"   ,tohs→[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→rtnat p₁ $ BoolMV         $ n₁ < n₂
  ("LT"   ,tohs→[IntMV p₁ i₁,IntMV p₂ i₂])         |p₁≡p₂→rtint p₁ $ BoolMV         $ i₁ < i₂
  ("LT"   ,tohs→[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→rtflt p₁ $ BoolMV         $ f₁ < f₂
  ("GT"   ,tohs→[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→rtnat p₁ $ BoolMV         $ n₁ > n₂
  ("GT"   ,tohs→[IntMV p₁ i₁,IntMV p₂ i₂])         |p₁≡p₂→rtint p₁ $ BoolMV         $ i₁ > i₂
  ("GT"   ,tohs→[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→rtflt p₁ $ BoolMV         $ f₁ > f₂
  ("LTE"  ,tohs→[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→rtnat p₁ $ BoolMV         $ n₁ ≤ n₂
  ("LTE"  ,tohs→[IntMV p₁ i₁,IntMV p₂ i₂])         |p₁≡p₂→rtint p₁ $ BoolMV         $ i₁ ≤ i₂
  ("LTE"  ,tohs→[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→rtflt p₁ $ BoolMV         $ f₁ ≤ f₂
  ("GTE"  ,tohs→[NatMV p₁ n₁,NatMV p₂ n₂])         |p₁≡p₂→rtnat p₁ $ BoolMV         $ n₁ ≥ n₂
  ("GTE"  ,tohs→[IntMV p₁ i₁,IntMV p₂ i₂])         |p₁≡p₂→rtint p₁ $ BoolMV         $ i₁ ≥ i₂
  ("GTE"  ,tohs→[FltMV p₁ f₁,FltMV p₂ f₂])         |p₁≡p₂→rtflt p₁ $ BoolMV         $ f₁ ≥ f₂
  ("COND" ,tohs→[BoolMV b,BoolMV b₁  ,BoolMV b₂  ])      →rtboo    $ BoolMV         $ if b then b₁ else b₂
  ("COND" ,tohs→[BoolMV b,NatMV p₁ n₁,NatMV p₂ n₂])|p₁≡p₂→rtnat p₁ $ NatMV p₁       $ if b then n₁ else n₂
  ("COND" ,tohs→[BoolMV b,IntMV p₁ i₁,IntMV p₂ i₂])|p₁≡p₂→rtint p₁ $ IntMV p₁       $ if b then i₁ else i₂
  ("COND" ,tohs→[BoolMV b,FltMV p₁ f₁,FltMV p₂ f₂])|p₁≡p₂→rtflt p₁ $ FltMV p₁       $ if b then f₁ else f₂
  ("COND" ,tohs→[BoolMV b,PrinMV p₁  ,PrinMV p₂  ])      →rtprn    $ PrinMV         $ if b then p₁ else p₂
  ("FLT"  ,tohs→[NatMV p n])                             →rtnat p  $ FltMV(pffri p) $ dbl n
  ("FLT"  ,tohs→[IntMV p n])                             →rtint p  $ FltMV(pffri p) $ dbl n
  ("ABS"  ,tohs→[IntMV p i])                             →rtint p  $ NatMV p        $ zabs i
  ("CEIL" ,tohs→[FltMV p f])                             →rtflt p  $ IntMV(pifrf p) $ ceiling f
  ("SQRT" ,tohs→[FltMV p f])                             →rtflt p  $ FltMV p        $ root f
  _ → throwIErrorCxt NotImplementedIError "interpPrim" $ frhs
    [ ("o",pretty o)
    , ("vs",pretty vs)
    ]
  where
    rtnat p = return ∘ (:*) (tnat p)
    rtint p = return ∘ (:*) (tint p)
    rtflt p = return ∘ (:*) (tflt p)
    rtboo = return ∘ (:*) tboo
    rtprn = return ∘ (:*) tprn
    pffri = fPrecFrIPrec
    pifrf = iPrecFrFPrec
