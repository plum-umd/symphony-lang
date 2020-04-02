module PSL.Interpreter.Primitives where

import UVMHS

import PSL.Interpreter.Types
import PSL.Interpreter.Truncating
import PSL.Interpreter.Pretty ()
import PSL.Syntax
import PSL.Interpreter.Json

valWithType ∷ Val → Val ∧ 𝕊
valWithType v = v :* getType v

multDepth ∷ Prot → 𝕊 → ℕ
multDepth p o = case (p, o) of
  (_, "TIMES") → 1
  (_, "GT") -> 1
  (_, "LT") -> 1
  (_, "EQ") -> 1
  (_, "GTE") -> 1
  (_, "LTE") -> 1
  _ → 0 -- To be updated

interpPrim ∷ (STACK) ⇒ 𝕊 → 𝐿 Val → IM (Val ∧ 𝕊)
interpPrim o vs = case (o,vs) of
  ("OR"      ,tohs → [BoolV b₁  ,BoolV b₂  ])           → return $ valWithType (BoolV   $ b₁ ⩔ b₂)
  ("AND"     ,tohs → [BoolV b₁  ,BoolV b₂  ])           → return $ valWithType (BoolV   $ b₁ ⩓ b₂)
  ("NOT"     ,tohs → [BoolV b])                         → return $ valWithType (BoolV   $ not b  )
  ("PLUS"    ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ valWithType (NatV p₁ $ trPrNat p₁ $ n₁ + n₂)
  ("PLUS"    ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ valWithType (IntV p₁ $ trPrInt p₁ $ i₁ + i₂)
  ("PLUS"    ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ valWithType (FltV p₁ $ f₁ + f₂)
  ("MINUS"   ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ valWithType (NatV p₁ $ trPrNat p₁ $ buPrNat p₁ n₁ - n₂)
  ("MINUS"   ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ valWithType (IntV p₁ $ trPrInt p₁ $ i₁ - i₂)
  ("MINUS"   ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ valWithType (FltV p₁ $ f₁ - f₂)
  ("TIMES"   ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ valWithType (NatV p₁ $ trPrNat p₁ $ n₁ × n₂)
  ("TIMES"   ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ valWithType (IntV p₁ $ trPrInt p₁ $ i₁ × i₂)
  ("TIMES"   ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ valWithType (FltV p₁ $ f₁ × f₂)
  ("EXP"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ valWithType (NatV p₁ $ trPrNat p₁ $ n₁ ^^ n₂)
  ("EXP"     ,tohs → [IntV p₁ i₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ valWithType (IntV p₁ $ trPrInt p₁ $ i₁ ^^ n₂)
  ("EXP"     ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ valWithType (FltV p₁ $ f₁ ^ f₂)
  ("DIV"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ valWithType (NatV p₁ $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ⌿ n₂)
  ("DIV"     ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ valWithType (IntV p₁ $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ⌿ i₂)
  ("DIV"     ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ valWithType (FltV p₁ $              if f₂ ≡ 0.0   then f₁ else f₁ / f₂)
  ("MOD"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ valWithType (NatV p₁ $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ÷ n₂)
  ("MOD"     ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ valWithType (IntV p₁ $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ÷ i₂)
  -- ("MOD"     ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ valWithType (FltV p₁ $              if f₂ ≡ 0.0   then f₁ else f₁ ÷ f₂)
  ("EQ"      ,tohs → [BoolV b₁  ,BoolV b₂  ])           → return $ valWithType (BoolV   $ b₁ ≡ b₂)
  ("EQ"      ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ (BoolV   $ n₁ ≡ n₂) :* "nat"⧺iprecisionSuffix p₁
  ("EQ"      ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ (BoolV   $ i₁ ≡ i₂) :* "int"⧺iprecisionSuffix p₁
  ("EQ"      ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ (BoolV   $ f₁ ≡ f₂) :* "flt"⧺fprecisionSuffix p₁
  ("EQ"      ,tohs → [PrinV ρev₁,PrinV ρev₂])           → return $ (BoolV   $ ρev₁ ≡ ρev₂) :* "prin"
  ("LT"      ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ (BoolV   $ n₁ < n₂) :* "nat"⧺iprecisionSuffix p₁
  ("LT"      ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ (BoolV   $ i₁ < i₂) :* "int"⧺iprecisionSuffix p₁
  ("LT"      ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ (BoolV   $ f₁ < f₂) :* "flt"⧺fprecisionSuffix p₁
  ("GT"      ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ (BoolV   $ n₁ > n₂) :* "nat"⧺iprecisionSuffix p₁
  ("GT"      ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ (BoolV   $ i₁ > i₂) :* "int"⧺iprecisionSuffix p₁
  ("GT"      ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ (BoolV   $ f₁ > f₂) :* "flt"⧺fprecisionSuffix p₁
  ("LTE"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ (BoolV   $ n₁ ≤ n₂) :* "nat"⧺iprecisionSuffix p₁
  ("LTE"     ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ (BoolV   $ i₁ ≤ i₂) :* "int"⧺iprecisionSuffix p₁
  ("LTE"     ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ (BoolV   $ f₁ ≤ f₂) :* "flt"⧺fprecisionSuffix p₁
  ("GTE"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ (BoolV   $ n₁ ≥ n₂) :* "nat"⧺iprecisionSuffix p₁
  ("GTE"     ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ (BoolV   $ i₁ ≥ i₂) :* "int"⧺iprecisionSuffix p₁
  ("GTE"     ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ (BoolV   $ f₁ ≥ f₂) :* "flt"⧺fprecisionSuffix p₁
  ("COND"    ,tohs → [BoolV b   ,BoolV b₁  ,BoolV b₂  ])           → return $ valWithType (BoolV    $ if b then b₁ else b₂)
  ("COND"    ,tohs → [BoolV b   ,NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ valWithType (NatV p₁  $ if b then n₁ else n₂)
  ("COND"    ,tohs → [BoolV b   ,IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ valWithType (IntV p₁  $ if b then i₁ else i₂)
  ("COND"    ,tohs → [BoolV b   ,FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ valWithType (FltV p₁  $ if b then f₁ else f₂)
  ("COND"    ,tohs → [BoolV b   ,PrinV p₁  ,PrinV p₂  ])           → return $ valWithType (PrinV    $ if b then p₁ else p₂)
  ("COND"    ,tohs → [BoolV b   ,PrinSetV ps₁,PrinV p₂]) | psize ps₁ ≡ 1 → let Some (p₁ :* _) = uncons𝑆 $ stream𝑃 ps₁ in return $ valWithType (PrinV $ if b then ValPEV p₁ else p₂)
  ("COND"    ,tohs → [BoolV b   ,PrinV p₁,PrinSetV ps₂]) | psize ps₂ ≡ 1 → let Some (p₂ :* _) = uncons𝑆 $ stream𝑃 ps₂ in return $ valWithType (PrinV $ if b then p₁ else ValPEV p₂)
  ("TO_FLT"  ,tohs → [NatV p n])                        → return $ (FltV (fPrecFrIPrec p) $ dbl n) :* "nat"⧺iprecisionSuffix p
  ("TO_FLT"  ,tohs → [IntV p n])                        → return $ (FltV (fPrecFrIPrec p) $ dbl n) :* "int"⧺iprecisionSuffix p
  ("ABS_VAL" ,tohs → [NatV p n])                        → return $ (NatV p n) :* "nat"⧺iprecisionSuffix p
  ("ABS_VAL" ,tohs → [IntV p i])                        → return $ (NatV p  $ zabs i) :* "int"⧺iprecisionSuffix p
  ("CEIL"    ,tohs → [FltV p f])                        → return $ (IntV (iPrecFrFPrec p) $ ceiling f) :* "flt"⧺fprecisionSuffix p
  ("SQRT"    ,tohs → [FltV p f])                        → return $ (FltV p  $ root f) :* "flt"⧺fprecisionSuffix p
  _ → throwIErrorCxt NotImplementedIError "interpPrim" $ frhs
    [ ("o",pretty o)
    , ("vs",pretty vs)
    ]
