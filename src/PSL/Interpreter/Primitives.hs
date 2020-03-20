module PSL.Interpreter.Primitives where

import UVMHS

import PSL.Interpreter.Types
import PSL.Interpreter.Truncating
import PSL.Interpreter.Pretty ()
import PSL.Syntax

interpPrim ∷ (STACK) ⇒ 𝕊 → 𝐿 Val → IM (Val ∧ 𝕊)
interpPrim o vs = case (o,vs) of
  ("OR"      ,tohs → [BoolV b₁  ,BoolV b₂  ])           → return $ let v = (BoolV   $ b₁ ⩔ b₂)                                         in v :* getType v
  ("AND"     ,tohs → [BoolV b₁  ,BoolV b₂  ])           → return $ let v = (BoolV   $ b₁ ⩓ b₂)                                         in v :* getType v
  ("NOT"     ,tohs → [BoolV b])                         → return $ let v = (BoolV   $ not b  )                                         in v :* getType v
  ("PLUS"    ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ let v = (NatV p₁ $ trPrNat p₁ $ n₁ + n₂)                            in v :* getType v
  ("PLUS"    ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ let v = (IntV p₁ $ trPrInt p₁ $ i₁ + i₂)                            in v :* getType v
  ("PLUS"    ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ let v = (FltV p₁ $ f₁ + f₂)                                         in v :* getType v
  ("MINUS"   ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ let v = (NatV p₁ $ trPrNat p₁ $ buPrNat p₁ n₁ - n₂)                 in v :* getType v
  ("MINUS"   ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ let v = (IntV p₁ $ trPrInt p₁ $ i₁ - i₂)                            in v :* getType v
  ("MINUS"   ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ let v = (FltV p₁ $ f₁ - f₂)                                         in v :* getType v
  ("TIMES"   ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ let v = (NatV p₁ $ trPrNat p₁ $ n₁ × n₂)                            in v :* getType v
  ("TIMES"   ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ let v = (IntV p₁ $ trPrInt p₁ $ i₁ × i₂)                            in v :* getType v
  ("TIMES"   ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ let v = (FltV p₁ $ f₁ × f₂)                                         in v :* getType v
  ("EXP"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ let v = (NatV p₁ $ trPrNat p₁ $ n₁ ^^ n₂)                           in v :* getType v
  ("EXP"     ,tohs → [IntV p₁ i₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ let v = (IntV p₁ $ trPrInt p₁ $ i₁ ^^ n₂)                           in v :* getType v
  ("EXP"     ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ let v = (FltV p₁ $ f₁ ^ f₂)                                         in v :* getType v
  ("DIV"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ let v = (NatV p₁ $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ⌿ n₂) in v :* getType v
  ("DIV"     ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ let v = (IntV p₁ $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ⌿ i₂) in v :* getType v
  ("DIV"     ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ let v = (FltV p₁ $              if f₂ ≡ 0.0   then f₁ else f₁ ⌿ f₂) in v :* getType v
  ("MOD"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ let v = (NatV p₁ $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ÷ n₂) in v :* getType v
  ("MOD"     ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ let v = (IntV p₁ $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ÷ i₂) in v :* getType v
  ("MOD"     ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ let v = (FltV p₁ $              if f₂ ≡ 0.0   then f₁ else f₁ ÷ f₂) in v :* getType v
  ("EQ"      ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ let v = (BoolV   $ n₁ ≡ n₂)                                         in v :* getType v
  ("EQ"      ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ let v = (BoolV   $ i₁ ≡ i₂)                                         in v :* getType v
  ("EQ"      ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ let v = (BoolV   $ f₁ ≡ f₂)                                         in v :* getType v
  ("EQ"      ,tohs → [PrinV ρev₁,PrinV ρev₂])           → return $ let v = (BoolV   $ ρev₁ ≡ ρev₂)                                     in v :* getType v
  ("LT"      ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ let v = (BoolV   $ n₁ < n₂)                                         in v :* getType v
  ("LT"      ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ let v = (BoolV   $ i₁ < i₂)                                         in v :* getType v
  ("LT"      ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ let v = (BoolV   $ f₁ < f₂)                                         in v :* getType v
  ("GT"      ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ let v = (BoolV   $ n₁ > n₂)                                         in v :* getType v
  ("GT"      ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ let v = (BoolV   $ i₁ > i₂)                                         in v :* getType v
  ("GT"      ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ let v = (BoolV   $ f₁ > f₂)                                         in v :* getType v
  ("LTE"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ let v = (BoolV   $ n₁ ≤ n₂)                                         in v :* getType v
  ("LTE"     ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ let v = (BoolV   $ i₁ ≤ i₂)                                         in v :* getType v
  ("LTE"     ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ let v = (BoolV   $ f₁ ≤ f₂)                                         in v :* getType v
  ("GTE"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ let v = (BoolV   $ n₁ ≥ n₂)                                         in v :* getType v
  ("GTE"     ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ let v = (BoolV   $ i₁ ≥ i₂)                                         in v :* getType v
  ("GTE"     ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ let v = (BoolV   $ f₁ ≥ f₂)                                         in v :* getType v
  ("COND"    ,tohs → [BoolV b   ,BoolV b₁  ,BoolV b₂  ])           → return $ let v = (BoolV   $ if b then b₁ else b₂)                 in v :* getType v
  ("COND"    ,tohs → [BoolV b   ,NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ let v = (NatV p₁ $ if b then n₁ else n₂)                 in v :* getType v
  ("COND"    ,tohs → [BoolV b   ,IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ let v = (IntV p₁ $ if b then i₁ else i₂)                 in v :* getType v
  ("COND"    ,tohs → [BoolV b   ,FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ let v = (FltV p₁ $ if b then f₁ else f₂)                 in v :* getType v
  ("TO_FLT"  ,tohs → [NatV p n])                        → return $ let v = (FltV (fPrecFrIPrec p) $ dbl n)                             in v :* getType v
  ("TO_FLT"  ,tohs → [IntV p n])                        → return $ let v = (FltV (fPrecFrIPrec p) $ dbl n)                             in v :* getType v
  ("ABS_VAL" ,tohs → [NatV p n])                        → return $ let v = (NatV p n)                                                  in v :* getType v
  ("ABS_VAL" ,tohs → [IntV p i])                        → return $ let v = (NatV p  $ zabs i)                                          in v :* getType v
  ("CEIL"    ,tohs → [FltV p f])                        → return $ let v = (IntV (iPrecFrFPrec p) $ ceiling f)                         in v :* getType v
  ("SQRT"    ,tohs → [FltV p f])                        → return $ let v = (FltV p  $ root f)                                          in v :* getType v
  _ → throwIErrorCxt NotImplementedIError "interpPrim" $ frhs
    [ ("o",pretty o)
    , ("vs",pretty vs)
    ]
