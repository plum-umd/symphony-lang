module PSL.Interpreter.Primitives where

import UVMHS

import PSL.Interpreter.Types
import PSL.Interpreter.Truncating
import PSL.Syntax

interpPrim ∷ (STACK) ⇒ 𝕊 → 𝐿 Val → IM Val
interpPrim o vs = case (o,vs) of
  ("OR"      ,tohs → [BoolV b₁  ,BoolV b₂  ])           → return $ BoolV   $ b₁ ⩔ b₂
  ("AND"     ,tohs → [BoolV b₁  ,BoolV b₂  ])           → return $ BoolV   $ b₁ ⩓ b₂
  ("PLUS"    ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ NatV p₁ $ trPrNat p₁ $ n₁ + n₂
  ("PLUS"    ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ IntV p₁ $ trPrInt p₁ $ i₁ + i₂
  ("MINUS"   ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ NatV p₁ $ trPrNat p₁ $ buPrNat p₁ n₁ - n₂
  ("MINUS"   ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ IntV p₁ $ trPrInt p₁ $ i₁ - i₂
  ("TIMES"   ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ NatV p₁ $ trPrNat p₁ $ n₁ × n₂
  ("TIMES"   ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ IntV p₁ $ trPrInt p₁ $ i₁ × i₂
  ("DIV"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ NatV p₁ $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ⌿ n₂
  ("DIV"     ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ IntV p₁ $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ⌿ i₂
  ("MOD"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ NatV p₁ $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ÷ n₂
  ("MOD"     ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ IntV p₁ $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ÷ i₂
  ("EQ"      ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ BoolV   $ n₁ ≡ n₂
  ("EQ"      ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ BoolV   $ i₁ ≡ i₂
  ("LT"      ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ BoolV   $ n₁ < n₂
  ("LT"      ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ BoolV   $ i₁ < i₂
  ("GT"      ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ BoolV   $ n₁ > n₂
  ("GT"      ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ BoolV   $ i₁ > i₂
  ("LTE"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ BoolV   $ n₁ ≤ n₂
  ("LTE"     ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ BoolV   $ i₁ ≤ i₂
  ("GTE"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ BoolV   $ n₁ ≥ n₂
  ("GTE"     ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ BoolV   $ i₁ ≥ i₂
  ("COND"    ,tohs → [BoolV b   ,v₁,v₂     ])           → return           $ if b then v₁ else v₂
  ("TO_FLT"  ,tohs → [IntV (FixedIPr prw prd) n])       → return $ FltV (FixedFPr (prw + prd)) $ dbl n
  ("TO_FLT"  ,tohs → [NatV (FixedIPr prw prd) n])       → return $ FltV (FixedFPr (prw + prd)) $ dbl n
  ("ABS_VAL" ,tohs → [IntV p i])                        → return $ NatV p  $ zabs i
  ("ABS_VAL" ,tohs → [NatV p n])                        → return $ NatV p n
  ("CEIL"    ,tohs → [FltV (FixedFPr pr) f])            → return $ IntV (FixedIPr pr 0) $ ceiling f
  ("SQRT"    ,tohs → [FltV p f])                        → return $ FltV p  $ root f
  _ → throwIErrorCxt NotImplementedIError "interpPrim" $ frhs
    [ ("o",pretty o)
    , ("vs",pretty vs)
    ]

