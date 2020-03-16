module PSL.Interpreter.Primitives where

import UVMHS

import PSL.Interpreter.Types
import PSL.Interpreter.Truncating
import PSL.Interpreter.Pretty ()
import PSL.Syntax

iprecisionSuffix ∷ IPrecision → 𝕊
iprecisionSuffix = \case
  InfIPr → ""
  FixedIPr n₁ n₂ → concat ["#",show𝕊 n₁,".",show𝕊 n₂]

fprecisionSuffix ∷ FPrecision → 𝕊
fprecisionSuffix (FixedFPr n) = concat ["#",show𝕊 n]

iPrecFrFPrec ∷ FPrecision → IPrecision
iPrecFrFPrec (FixedFPr pr) = FixedIPr pr 0

fPrecFrIPrec ∷ IPrecision → FPrecision
fPrecFrIPrec = \case
  InfIPr → FixedFPr 64
  FixedIPr n₁ n₂ → FixedFPr $ n₁ + n₂

interpPrim ∷ (STACK) ⇒ 𝕊 → 𝐿 Val → IM (Val ∧ 𝕊)
interpPrim o vs = case (o,vs) of
  ("OR"      ,tohs → [BoolV b₁  ,BoolV b₂  ])           → return $ (BoolV   $ b₁ ⩔ b₂)                                         :* "bool"
  ("AND"     ,tohs → [BoolV b₁  ,BoolV b₂  ])           → return $ (BoolV   $ b₁ ⩓ b₂)                                         :* "bool"
  ("NOT"     ,tohs → [BoolV b])                         → return $ (BoolV   $ not b  )                                         :* "bool"
  ("PLUS"    ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ (NatV p₁ $ trPrNat p₁ $ n₁ + n₂)                            :* "nat"⧺iprecisionSuffix p₁
  ("PLUS"    ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ (IntV p₁ $ trPrInt p₁ $ i₁ + i₂)                            :* "int"⧺iprecisionSuffix p₁
  ("PLUS"    ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ (FltV p₁ $ f₁ + f₂)                                         :* "flt"⧺fprecisionSuffix p₁
  ("MINUS"   ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ (NatV p₁ $ trPrNat p₁ $ buPrNat p₁ n₁ - n₂)                 :* "nat"⧺iprecisionSuffix p₁
  ("MINUS"   ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ (IntV p₁ $ trPrInt p₁ $ i₁ - i₂)                            :* "int"⧺iprecisionSuffix p₁
  ("MINUS"   ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ (FltV p₁ $ f₁ - f₂)                                         :* "flt"⧺fprecisionSuffix p₁
  ("TIMES"   ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ (NatV p₁ $ trPrNat p₁ $ n₁ × n₂)                            :* "nat"⧺iprecisionSuffix p₁
  ("TIMES"   ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ (IntV p₁ $ trPrInt p₁ $ i₁ × i₂)                            :* "int"⧺iprecisionSuffix p₁
  ("TIMES"   ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ (FltV p₁ $ f₁ × f₂)                                         :* "flt"⧺fprecisionSuffix p₁
  ("EXP"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ (NatV p₁ $ trPrNat p₁ $ n₁ ^^ n₂)                           :* "nat"⧺iprecisionSuffix p₁
  ("EXP"     ,tohs → [IntV p₁ i₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ (IntV p₁ $ trPrInt p₁ $ i₁ ^^ n₂)                           :* "int"⧺iprecisionSuffix p₁
  ("EXP"     ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ (FltV p₁ $ f₁ ^ f₂)                                         :* "flt"⧺fprecisionSuffix p₁
  ("DIV"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ (NatV p₁ $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ⌿ n₂) :* "nat"⧺iprecisionSuffix p₁
  ("DIV"     ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ (IntV p₁ $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ⌿ i₂) :* "int"⧺iprecisionSuffix p₁
  ("DIV"     ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ (FltV p₁ $              if f₂ ≡ 0.0   then f₁ else f₁ ⌿ f₂) :* "flt"⧺fprecisionSuffix p₁
  ("MOD"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ (NatV p₁ $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ÷ n₂) :* "nat"⧺iprecisionSuffix p₁
  ("MOD"     ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ (IntV p₁ $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ÷ i₂) :* "int"⧺iprecisionSuffix p₁
  ("MOD"     ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ (FltV p₁ $              if f₂ ≡ 0.0   then f₁ else f₁ ÷ f₂) :* "flt"⧺fprecisionSuffix p₁
  ("EQ"      ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ (BoolV   $ n₁ ≡ n₂)                                         :* "nat"⧺iprecisionSuffix p₁
  ("EQ"      ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ (BoolV   $ i₁ ≡ i₂)                                         :* "int"⧺iprecisionSuffix p₁
  ("EQ"      ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ (BoolV   $ f₁ ≡ f₂)                                         :* "flt"⧺fprecisionSuffix p₁
  ("EQ"      ,tohs → [PrinV ρev₁,PrinV ρev₂])           → return $ (BoolV   $ ρev₁ ≡ ρev₂)                                     :* "prin"
  ("LT"      ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ (BoolV   $ n₁ < n₂)                                         :* "nat"⧺iprecisionSuffix p₁
  ("LT"      ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ (BoolV   $ i₁ < i₂)                                         :* "int"⧺iprecisionSuffix p₁
  ("LT"      ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ (BoolV   $ f₁ < f₂)                                         :* "flt"⧺fprecisionSuffix p₁
  ("GT"      ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ (BoolV   $ n₁ > n₂)                                         :* "nat"⧺iprecisionSuffix p₁
  ("GT"      ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ (BoolV   $ i₁ > i₂)                                         :* "int"⧺iprecisionSuffix p₁
  ("GT"      ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ (BoolV   $ f₁ > f₂)                                         :* "flt"⧺fprecisionSuffix p₁
  ("LTE"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ (BoolV   $ n₁ ≤ n₂)                                         :* "nat"⧺iprecisionSuffix p₁
  ("LTE"     ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ (BoolV   $ i₁ ≤ i₂)                                         :* "int"⧺iprecisionSuffix p₁
  ("LTE"     ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ (BoolV   $ f₁ ≤ f₂)                                         :* "flt"⧺fprecisionSuffix p₁
  ("GTE"     ,tohs → [NatV p₁ n₁,NatV p₂ n₂]) | p₁ ≡ p₂ → return $ (BoolV   $ n₁ ≥ n₂)                                         :* "nat"⧺iprecisionSuffix p₁
  ("GTE"     ,tohs → [IntV p₁ i₁,IntV p₂ i₂]) | p₁ ≡ p₂ → return $ (BoolV   $ i₁ ≥ i₂)                                         :* "int"⧺iprecisionSuffix p₁
  ("GTE"     ,tohs → [FltV p₁ f₁,FltV p₂ f₂]) | p₁ ≡ p₂ → return $ (BoolV   $ f₁ ≥ f₂)                                         :* "flt"⧺fprecisionSuffix p₁
  ("COND"    ,tohs → [BoolV b   ,v₁,v₂     ])           → return $ (if b then v₁ else v₂)                                      :* "bool" -- TODO: change to branch type
  ("TO_FLT"  ,tohs → [NatV p n])                        → return $ (FltV (fPrecFrIPrec p) $ dbl n)                             :* "nat"⧺iprecisionSuffix p
  ("TO_FLT"  ,tohs → [IntV p n])                        → return $ (FltV (fPrecFrIPrec p) $ dbl n)                             :* "int"⧺iprecisionSuffix p
  ("ABS_VAL" ,tohs → [NatV p n])                        → return $ (NatV p n)                                                  :* "nat"⧺iprecisionSuffix p
  ("ABS_VAL" ,tohs → [IntV p i])                        → return $ (NatV p  $ zabs i)                                          :* "int"⧺iprecisionSuffix p
  ("CEIL"    ,tohs → [FltV p f])                        → return $ (IntV (iPrecFrFPrec p) $ ceiling f)                         :* "flt"⧺fprecisionSuffix p
  ("SQRT"    ,tohs → [FltV p f])                        → return $ (FltV p  $ root f)                                          :* "flt"⧺fprecisionSuffix p
  _ → throwIErrorCxt NotImplementedIError "interpPrim" $ frhs
    [ ("o",pretty o)
    , ("vs",pretty vs)
    ]
