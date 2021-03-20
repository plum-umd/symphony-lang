module PSL.Interpreter.MPCVal where

import UVMHS

import PSL.Syntax
import PSL.Interpreter.Types

import PSL.Interpreter.Share
import PSL.Interpreter.Val

valPFrMPCVal ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → MPCVal → IM ValP
valPFrMPCVal φ ρvs = \case
  DefaultMV → valPFrVal DefaultV
  BaseMV sh → return $ ShareVP φ ρvs $ BaseMV sh
  PairMV v̂₁ v̂₂ → do
    ṽ₁ ← valPFrMPCVal φ ρvs v̂₁
    ṽ₂ ← valPFrMPCVal φ ρvs v̂₂
    valPFrVal $ PairV ṽ₁ ṽ₂
  SumMV sh₁ v̂₂ v̂₃ → return $ ShareVP φ ρvs $ SumMV sh₁ v̂₂ v̂₃
  NilMV → valPFrVal NilV
  ConsMV v̂₁ v̂₂ → do
    ṽ₁ ← valPFrMPCVal φ ρvs v̂₁
    ṽ₂ ← valPFrMPCVal φ ρvs v̂₂
    valPFrVal $ ConsV ṽ₁ ṽ₂
  BulMV → valPFrVal $ BaseV BulBV

muxMPCVal ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ Share → MPCVal → MPCVal → P p → SProt p → IM MPCVal
muxMPCVal sh₁ v̂₂ v̂₃ p sp = case (v̂₂, v̂₃) of
  (DefaultMV, DefaultMV) → return DefaultMV
  (DefaultMV, BaseMV sh₃) → do
    pv₁ ← unwrapShare sh₁ sp
    pv₃ ← unwrapShare sh₃ sp
    τ₂  ← typeOf p pv₃
    pv₂ ← defaultOf p τ₂
    pv' ← exePrim p CondO $ frhs [ pv₁, pv₂, pv₃ ]
    return $ BaseMV $ Share sp pv'
{-  (BaseMV sh₂, DefaultMV) →
    withShare2 sh₁ sh₂ $ \ p sp pv₁ pv₂ → do
    τ₃  ← typeOf p pv₂
    pv₃ ← defaultOf p τ₃
    pv' ← exePrim p CondO $ frhs [ pv₁, pv₂, pv₃ ]
    return $ BaseMV $ Share sp pv'
  (BaseMV c₂, BaseMV c₃) →
    withShare3 sh₁ sh₂ sh₃ $ \ p sp pv₁ pv₂ pv₃ → do
    pv' ← exePrim p CondO $ frhs [ pv₁, pv₂, pv₃ ]
    return $ BaseMV $ Share sp pv'
  (DefaultMV, PairMV v̂₃₁ v̂₃₂) → do
    v̂'₁ ← muxMPCVal sh₁ DefaultMV v̂₃₁
    v̂'₂ ← muxMPCVal sh₁ DefaultMV v̂₃₂
    return $ PairMV v̂'₁ v̂'₂
  (PairMV v̂₂₁ v̂₂₂, DefaultMV) → do
    v̂'₁ ← muxMPCVal sh₁ v̂₂₁ DefaultMV
    v̂'₂ ← muxMPCVal sh₁ v̂₂₂ DefaultMV
    return $ PairMV v̂'₁ v̂'₂
  (PairMV v̂₂₁ v̂₂₂, PairMV v̂₃₁ v̂₃₂) → do
    v̂'₁ ← muxMPCVal sh₁ v̂₂₁ v̂₃₁
    v̂'₂ ← muxMPCVal sh₁ v̂₂₂ v̂₃₂
    return $ PairMV v̂'₁ v̂'₂
  (DefaultMV, SumMV sh₃ v̂₃₁ v̂₃₂) →
    withShare2 sh₁ sh₃ $ \ p sp pv₁ pv₃ → do
    def ← defaultOf p 𝔹T
    pv' ← exePrim p CondO $ frhs [ pv₁, def, pv₃ ]
    v̂'₁ ← muxMPCVal sh₁ DefaultMV v̂₃₁
    v̂'₂ ← muxMPCVal sh₁ DefaultCV v̂₃₂
    return $ SumMV (Share sp pv') v̂'₁ v̂'₂
  (SumCV sh₂ v̂₂₁ v̂₂₂, DefaultCV) →
    withShare2 sh₁ sh₂ $ \ p sp pv₁ pv₂ → do
    def ← defaultOf p 𝔹T
    pv' ← exePrim p CondO $ frhs [ pv₁, pv₂, def ]
    v̂'₁ ← muxMPCVal sh₁ v̂₂₁ DefaultCV
    v̂'₂ ← muxMPCVal sh₁ v̂₂₂ DefaultCV
    return $ SumMV (Share sp pv') v̂'₁ v̂'₂
  (SumMV sh₂ v̂₂₁ v̂₂₂, SumMV sh₃ v̂₃₁ v̂₃₂) → do
    withShare3 sh₁ sh₂ sh₃ $ \ p sp pv₁ pv₂ pv₃ → do
    pv' ← exePrim p CondO $ frhs [ pv₁, pv₂, pv₃ ]
    v̂'₁ ← muxMPCVal sh₁ v̂₂₁ v̂₃₁
    v̂'₂ ← muxMPCVal sh₁ v̂₂₂ v̂₃₂
    return $ SumMV (Share sp pv') v̂'₁ v̂'₂
  (DefaultMV, NilMV) → return NilMV
  (NilMV, DefaultMV) → return NilMV
  (NilMV, NilMV) → return NilMV
  (DefaultMV, ConsMV v̂₃₁ v̂₃₂) → do
    v̂'₁ ← muxMPCVal sh₁ DefaultMV v̂₃₁
    v̂'₂ ← muxMPCVal sh₁ DefaultMV v̂₃₂
    return $ ConsMV v̂'₁ v̂'₂
  (ConsMV v̂₂₁ v̂₂₂, DefaultMV) → do
    v̂'₁ ← muxMPCVal sh₁ v̂₂₁ DefaultMV
    v̂'₂ ← muxMPCVal sh₁ v̂₂₂ DefaultMV
    return $ ConsMV v̂'₁ v̂'₂
  (ConsMV v̂₂₁ v̂₂₂, ConsMV v̂₃₁ v̂₃₂) → do
    v̂'₁ ← muxMPCVal sh₁ v̂₂₁ v̂₃₁
    v̂'₂ ← muxMPCVal sh₁ v̂₂₂ v̂₃₂
    return $ ConsMV v̂'₁ v̂'₂
  (DefaultMV, BulMV) → return BulMV
  (BulMV, DefaultMV) → return BulMV
  (BulMV, BulMV) → return BulMV
  _ → throwIErrorCxt TypeIError "muxMPCVal: MPC values v̂₂ and v̂₃ have different shapes." $ frhs
    [ ("v̂₂", pretty cv₂)
    , ("v̂₃", pretty cv₃)
    ] -}

sumMPCVal ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ MPCVal → MPCVal → P p → SProt p → IM MPCVal
sumMPCVal v̂₁ v̂₂ p sp = case (v̂₁, v̂₂) of
  (_, DefaultMV) → return v̂₁
  (DefaultMV, _) → return v̂₂
  (BaseMV sh₁, BaseMV sh₂) → do
    pv₁ ← unwrapShare sh₁ sp
    pv₂ ← unwrapShare sh₂ sp
    pv' ← exePrim p PlusO $ frhs [ pv₁, pv₂ ]
    return $ BaseMV $ Share sp pv'
{-
  (PairCV cv₁₁ cv₁₂, PairCV cv₂₁ cv₂₂) → do
    cv'₁ ← sumCktVal cv₁₁ cv₂₁
    cv'₂ ← sumCktVal cv₁₂ cv₂₂
    return $ PairCV cv'₁ cv'₂
  (SumCV c₁ cv₁₁ cv₁₂, SumCV c₂ cv₂₁ cv₂₂) → do
    c' ← orCkt c₁ c₂
    cv'₁ ← sumCktVal cv₁₁ cv₂₁
    cv'₂ ← sumCktVal cv₁₂ cv₂₂
    return $ SumCV c' cv'₁ cv'₂
  (NilCV, NilCV) → return NilCV
  (ConsCV cv₁₁ cv₁₂, ConsCV cv₂₁ cv₂₂) → do
    cv'₁ ← sumCktVal cv₁₁ cv₂₁
    cv'₂ ← sumCktVal cv₁₂ cv₂₂
    return $ ConsCV cv'₁ cv'₂
  (BulCV, BulCV) → return BulCV
  _ → throwIErrorCxt TypeIError "sumCktVal: circuit values cv₁ and cv₂ have different shapes." $ frhs
    [ ("cv₁", pretty cv₁)
    , ("cv₂", pretty cv₂)
    ] -}
