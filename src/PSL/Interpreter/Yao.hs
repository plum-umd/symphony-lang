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

revealC ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ 𝑃 PrinVal → PrinVal → 𝑃 PrinVal → MPCVal 'Yao2P → m Val
revealC ρvsC ρvCanon ρvsR = \case
  BaseMV (BoolEV eb)   → map (BaseV ∘ BoolBV) $ empBitReveal eb ρvsC ρvCanon
  BaseMV (IntEV pr ez) → map (BaseV ∘ (IntBV pr) ∘ (trPrInt pr)) $ empIntegerReveal ez ρvsC ρvCanon
  BaseMV (NatEV pr en) → map (BaseV ∘ (NatBV pr) ∘ (trPrNat pr) ∘ HS.fromIntegral) $ empIntegerReveal en ρvsC ρvCanon
  PairMV v̂₁ v̂₂ → do
    v₁ ← revealC ρvsC ρvCanon ρvsR v̂₁
    v₂ ← revealC ρvsC ρvCanon ρvsR v̂₂
    return $ PairV (toValP v₁) (toValP v₂)
  v̂ → throwIErrorCxt NotImplementedIError "but why tho" $ frhs [ ("v̂", pretty v̂) ]
  where toValP = SSecVP (SecM ρvsR)

yaoCheck2P ∷ (Monad m, MonadReader ICxt m, MonadError IError m) ⇒ 𝑃 PrinVal → m ()
yaoCheck2P ρvsC = do
  guardErr (count ρvsC ≡ 2) $
    throwIErrorCxt TypeIError "yaoCheckShare: count ρvsC ≢ 2" $ frhs
    [ ("ρvsC", pretty ρvsC)
    ]

yaoCheckShare ∷ (Monad m, MonadReader ICxt m, MonadError IError m) ⇒ PrinVal → 𝑃 PrinVal → m ()
yaoCheckShare ρvS ρvsC = do
  yaoCheck2P ρvsC
  guardErr (ρvS ∈ ρvsC) $
    throwIErrorCxt TypeIError "yaoCheckShare: ρvS ∉ ρvsC" $ frhs
    [ ("ρvS", pretty ρvS)
    , ("ρvsC", pretty ρvsC)
    ]

yaoCheckReveal ∷ (Monad m, MonadReader ICxt m, MonadError IError m) ⇒ 𝑃 PrinVal → 𝑃 PrinVal → m ()
yaoCheckReveal ρvsC ρvsR =  do
  yaoCheck2P ρvsC
  guardErr (ρvsR ∩ ρvsC ≢ pø) $
    throwIErrorCxt TypeIError "yaoCheckReveal: ρvsR ∩ ρvsC ≡ pø" $ frhs
    [ ("ρvsR", pretty ρvsR)
    , ("ρvsC", pretty ρvsC)
    ]

instance Protocol 'Yao2P where
  type ProtocolVal 'Yao2P = EMPVal

  typeOf ∷ P 'Yao2P → EMPVal → BaseType
  typeOf _p = empType

  shareBaseVal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'Yao2P → 𝑃 PrinVal → PrinVal → BaseVal → m EMPVal
  shareBaseVal _p ρvs ρv bv = do
    yaoCheckShare ρv ρvs
    empShare ρvs (single ρv) bv

  shareUnk ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'Yao2P → 𝑃 PrinVal → PrinVal → BaseType → m EMPVal
  shareUnk p ρvs ρv bτ = do
    yaoCheckShare ρv ρvs
    empShare ρvs (single ρv) (defaultBaseValOf bτ)

  embedBaseVal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'Yao2P → 𝑃 PrinVal → BaseVal → m EMPVal
  embedBaseVal _p ρvs bv = do
    yaoCheck2P ρvs
    empShare ρvs ρvs bv

  exePrim ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'Yao2P → 𝑃 PrinVal → Op → 𝐿 EMPVal → m EMPVal
  exePrim _p ρvs op evs = do
    yaoCheck2P ρvs
    case (op, tohs evs) of
      (NotO, [ BoolEV eb₁ ]) → map BoolEV $ io $ empBitNot eb₁
      (AndO, [ BoolEV eb₁, BoolEV eb₂ ]) → map BoolEV $ io $ empBitAnd eb₁ eb₂
      (CondO, [ BoolEV eb₁, BoolEV eb₂, BoolEV eb₃ ]) → map BoolEV $ io $ empBitCond eb₁ eb₂ eb₃
      (PlusO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerAdd ez₁ ez₂
      (MinusO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerSub ez₁ ez₂
      (TimesO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerMult ez₁ ez₂
      (DivO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerDiv ez₁ ez₂
      (ModO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerMod ez₁ ez₂
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
    yaoCheckReveal ρvsC ρvsR
    me ← whoAmI
    ρvCanon :* _ ← fromSomeCxt $ pmin $ ρvsC ∩ ρvsR
    if (me ∈ ρvsC) then do                                                     -- If I am one of the MPC parties...
      v ← revealC ρvsC ρvCanon ρvsR v̂                                          --   Do an EMP reveal to the canonical party only.
      when (me ≡ ρvCanon) $ eachWith (sendEncValR v) $ ρvsR ∖ (single ρvCanon) --   Canonical party encrypted sends the actual value to everyone else who should get it...
      if (me ≡ ρvCanon) then                                                   --   Canonical party just returns the value they received from EMP reveal
        return v
      else if (me ∈ ρvsR) then                                                 --   Non-Canonical party either encrypted receives the value if they should get it, or doesn't.
        recvEncValR ρvCanon
      else
        return UnknownV
    else if (me ∈ ρvsR) then                                                   -- Otherwise, I am NOT one of the MPC parties...
      recvEncValR ρvCanon                                                      --   So I should encrypted receive the value from the Canonical party
    else                                                                       -- Only the parties in ρvsC ∪ ρvsR should ever run this code, but just in case...
      impossibleCxt
