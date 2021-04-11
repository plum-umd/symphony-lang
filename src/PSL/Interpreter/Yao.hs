module PSL.Interpreter.Yao where

import UVMHS
import AddToUVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Lens
import PSL.Interpreter.Error
import PSL.Interpreter.Truncating

import PSL.Interpreter.EMP
import PSL.Interpreter.Send

import qualified Prelude as HS

revealC ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ 𝑃 PrinVal → 𝑃 PrinVal → MPCVal 'Yao2P → m Val
revealC ρvsC ρvsR = \case
  BaseMV (BoolEV eb)   → map (BaseV ∘ BoolBV) $ empBitReveal eb ρvsC ρvsCAndR  -- Both compute parties must perform reveal, regardless of whether they are being revealed to
  BaseMV (IntEV pr ez) → map (BaseV ∘ (IntBV pr) ∘ (trPrInt pr)) $ empIntegerReveal ez ρvsC ρvsCAndR
  BaseMV (NatEV pr en) → map (BaseV ∘ (NatBV pr) ∘ (trPrNat pr) ∘ HS.fromIntegral) $ empIntegerReveal en ρvsC ρvsCAndR
  PairMV v̂₁ v̂₂ → do
    v₁ ← revealC ρvsC ρvsR v̂₁
    v₂ ← revealC ρvsC ρvsR v̂₂
    return $ PairV (toValP v₁) (toValP v₂)
  v̂ → throwIErrorCxt NotImplementedIError "but why tho" $ frhs [ ("v̂", pretty v̂) ]
  where ρvsCAndR = ρvsC ∩ ρvsR
        toValP = SSecVP (SecM ρvsR)

instance Protocol 'Yao2P where
  type ProtocolVal 'Yao2P = EMPVal

  typeOf ∷ P 'Yao2P → EMPVal → BaseType
  typeOf _p = empType

  shareBaseVal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'Yao2P → 𝑃 PrinVal → PrinVal → BaseVal → m EMPVal
  shareBaseVal _p ρvs ρv bv = do
    empShare ρvs (single ρv) bv

  shareUnk ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'Yao2P → 𝑃 PrinVal → PrinVal → BaseType → m EMPVal
  shareUnk p ρvs ρv bτ = do
    empShare ρvs (single ρv) (defaultBaseValOf bτ)

  embedBaseVal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'Yao2P → 𝑃 PrinVal → BaseVal → m EMPVal
  embedBaseVal _p ρvs bv = empShare ρvs ρvs bv

  exePrim ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'Yao2P → 𝑃 PrinVal → Op → 𝐿 EMPVal → m EMPVal
  exePrim _p ρvs op evs = case (op, tohs evs) of
    (NotO, [ BoolEV eb₁ ]) → map BoolEV $ io $ empBitNot eb₁
    (AndO, [ BoolEV eb₁, BoolEV eb₂ ]) → map BoolEV $ io $ empBitAnd eb₁ eb₂
    (CondO, [ BoolEV eb₁, BoolEV eb₂, BoolEV eb₃ ]) → map BoolEV $ io $ empBitCond eb₁ eb₂ eb₃
    (PlusO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerAdd ez₁ ez₂
    (MinusO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerSub ez₁ ez₂
    (TimesO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerMult ez₁ ez₂
    (DivO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerDiv ez₁ ez₂
    (EqO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map BoolEV $ io $ empIntegerEq ez₁ ez₂
    (LTO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map BoolEV $ io $ empIntegerLt ez₁ ez₂
    (GTO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map BoolEV $ io $ empIntegerGt ez₁ ez₂
    (CondO, [ BoolEV eb₁, IntEV pr₁ ez₁, IntEV pr₂ ez₂]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerCond eb₁ ez₁ ez₂
    (PlusO, [ NatEV pr₁ en₁, NatEV pr₂ en₂ ]) | pr₁ ≡ pr₂ → map (NatEV pr₁) $ io $ empIntegerAdd en₁ en₂
    (EqO, [ NatEV pr₁ en₁, NatEV pr₂ en₂ ]) | pr₁ ≡ pr₂ → map BoolEV $ io $ empIntegerEq en₁ en₂
    (CondO, [ BoolEV eb₁, NatEV pr₁ en₁, NatEV pr₂ en₂]) | pr₁ ≡ pr₂ → map (NatEV pr₁) $ io $ empIntegerCond eb₁ en₁ en₂
    _ → throwIErrorCxt NotImplementedIError "comin up soon boss" $ frhs [ ("op", pretty op), ("evs", pretty evs) ]

  reveal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'Yao2P → 𝑃 PrinVal → 𝑃 PrinVal → MPCVal 'Yao2P → m Val
  reveal p ρvsC ρvsR v̂ = do
    lm ← askL iCxtLocalModeL
    me ← fromSomeCxt $ view (one𝑃L ⊚ secML) lm -- Who am I?
    let ρvsCAndR = ρvsC ∩ ρvsR
    let ρvsRNotC = ρvsR ∖ ρvsC
    ρvCanon :* _ ← error𝑂 (pmin $ ρvsCAndR) $ throwIErrorCxt NotImplementedIError "oof" $ frhs [ ("ρvsCAndR", pretty ρvsCAndR) ]
    if me ∈ ρvsC then do
      v ← revealC ρvsC ρvsR v̂
      when (me ≡ ρvCanon) $ eachWith (sendValR v) ρvsRNotC -- Canonical compute party shares and then reveals with each non-compute party
      return $ if me ∈ ρvsCAndR then v else UnknownV
    else
      recvValR ρvCanon
