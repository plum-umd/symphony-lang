module PSL.Interpreter.Primitives where

import UVMHS

import PSL.Interpreter.Types
import PSL.Interpreter.Truncating
import PSL.Interpreter.Pretty ()
import PSL.Syntax

valWithType ∷ Val → Val ∧ 𝕊
valWithType v = v :* getType v

multDepth ∷ Prot → 𝕊 → ℕ
multDepth p o = case (p, o) of
  (_, "TIMES") → 1
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
  ("DIV"     ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ valWithType (FltV p₁ $              if f₂ ≡ 0.0   then f₁ else f₁ ⌿ f₂)
  ("MOD"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ valWithType (NatV p₁ $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ÷ n₂)
  ("MOD"     ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ valWithType (IntV p₁ $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ÷ i₂)
  ("MOD"     ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ valWithType (FltV p₁ $              if f₂ ≡ 0.0   then f₁ else f₁ ÷ f₂)
  ("EQ"      ,tohs → [BoolV b₁  ,BoolV b₂  ])           → return $ valWithType (BoolV   $ b₁ ≡ b₂)
  ("EQ"      ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ valWithType (BoolV   $ n₁ ≡ n₂)
  ("EQ"      ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ valWithType (BoolV   $ i₁ ≡ i₂)
  ("EQ"      ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ valWithType (BoolV   $ f₁ ≡ f₂)
  ("EQ"      ,tohs → [PrinV ρev₁,PrinV ρev₂])           → return $ valWithType (BoolV   $ ρev₁ ≡ ρev₂)
  ("LT"      ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ valWithType (BoolV   $ n₁ < n₂)
  ("LT"      ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ valWithType (BoolV   $ i₁ < i₂)
  ("LT"      ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ valWithType (BoolV   $ f₁ < f₂)
  ("GT"      ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ valWithType (BoolV   $ n₁ > n₂)
  ("GT"      ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ valWithType (BoolV   $ i₁ > i₂)
  ("GT"      ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ valWithType (BoolV   $ f₁ > f₂)
  ("LTE"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ valWithType (BoolV   $ n₁ ≤ n₂)
  ("LTE"     ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ valWithType (BoolV   $ i₁ ≤ i₂)
  ("LTE"     ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ valWithType (BoolV   $ f₁ ≤ f₂)
  ("GTE"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ valWithType (BoolV   $ n₁ ≥ n₂)
  ("GTE"     ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ valWithType (BoolV   $ i₁ ≥ i₂)
  ("GTE"     ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ valWithType (BoolV   $ f₁ ≥ f₂)
  ("COND"    ,tohs → [BoolV b   ,BoolV b₁  ,BoolV b₂  ])           → return $ valWithType (BoolV    $ if b then b₁ else b₂)
  ("COND"    ,tohs → [BoolV b   ,NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ valWithType (NatV p₁  $ if b then n₁ else n₂)
  ("COND"    ,tohs → [BoolV b   ,IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ valWithType (IntV p₁  $ if b then i₁ else i₂)
  ("COND"    ,tohs → [BoolV b   ,FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ valWithType (FltV p₁  $ if b then f₁ else f₂)
  ("COND"    ,tohs → [BoolV b   ,PrinV p₁  ,PrinV p₂  ])           → return $ valWithType (PrinV    $ if b then p₁ else p₂)
  ("COND"    ,tohs → [BoolV b   ,PrinSetV ps₁,PrinV p₂]) | psize ps₁ ≡ 1 → let Some (p₁ :* _) = uncons𝑆 $ stream𝑃 ps₁ in return $ valWithType (PrinV $ if b then ValPEV p₁ else p₂)
  ("COND"    ,tohs → [BoolV b   ,PrinV p₁,PrinSetV ps₂]) | psize ps₂ ≡ 1 → let Some (p₂ :* _) = uncons𝑆 $ stream𝑃 ps₂ in return $ valWithType (PrinV $ if b then p₁ else ValPEV p₂)
  ("TO_FLT"  ,tohs → [NatV p n])                        → return $ valWithType (FltV (fPrecFrIPrec p) $ dbl n)
  ("TO_FLT"  ,tohs → [IntV p n])                        → return $ valWithType (FltV (fPrecFrIPrec p) $ dbl n)
  ("ABS_VAL" ,tohs → [NatV p n])                        → return $ valWithType (NatV p n)
  ("ABS_VAL" ,tohs → [IntV p i])                        → return $ valWithType (NatV p  $ zabs i)
  ("CEIL"    ,tohs → [FltV p f])                        → return $ valWithType (IntV (iPrecFrFPrec p) $ ceiling f)
  ("SQRT"    ,tohs → [FltV p f])                        → return $ valWithType (FltV p  $ root f)
  _ → throwIErrorCxt NotImplementedIError "interpPrim" $ frhs
    [ ("o",pretty o)
    , ("vs",pretty vs)
    ]
