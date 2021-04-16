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

import Network.Socket (PortNumber)

import qualified Prelude as HS

yaoCheck2P ∷ (Monad m, MonadReader ICxt m, MonadError IError m) ⇒ 𝑃 PrinVal → m ()
yaoCheck2P ρvsC = do
  guardErr (count ρvsC ≡ 2) $
    throwIErrorCxt TypeIError "yaoCheck2P: count ρvsC ≢ 2" $ frhs
    [ ("ρvsC", pretty ρvsC)
    ]

yaoCheck ∷ (Monad m, MonadReader ICxt m, MonadError IError m) ⇒ PrinVal → 𝑃 PrinVal → m ()
yaoCheck ρv ρvsC = do
  yaoCheck2P ρvsC
  guardErr (ρv ∈ ρvsC) $
    throwIErrorCxt TypeIError "yaoCheck: ρv ∉ ρvsC" $ frhs
    [ ("ρv", pretty ρvsC)
    , ("ρvsC", pretty ρvsC)
    ]

serializePrec ∷ (Monad m, MonadReader ICxt m, MonadError IError m) ⇒ IPrecision → m HS.Int
serializePrec = \case
  FixedIPr 64 0 → return $ HS.fromIntegral 64
  pr → throwIErrorCxt NotImplementedIError "[Yao] serializePrec: precision pr not supported" $ frhs [ ("pr", pretty pr) ]

getAlice ∷ 𝑃 PrinVal → PrinVal
getAlice ρvsC = alice
  where alice :* _ = fromSome $ pmin ρvsC

serializePrin ∷ PrinVal → 𝑃 PrinVal → HS.Int
serializePrin ρv ρvsC = if ρv ≡ alice then HS.fromIntegral 1 else HS.fromIntegral 2
  where alice = getAlice ρvsC

getOther ∷ (Monad m, MonadReader ICxt m, MonadError IError m) ⇒ PrinVal → 𝑃 PrinVal → m PrinVal
getOther ρv ρvs = fromSomeCxt $ view one𝑃L $ ρvs ∖ (single𝑃 ρv)

handleSession ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ 𝑃 PrinVal → m EMPSession
handleSession ρvsC = do
  me   ← whoAmI
  them ← getOther me ρvsC
  pptraceM them
  sessions ← getL iStateSessionsYaoL
  case sessions ⋕? them of
    None → do
      portMap ← getPortMap portYao
      let addr = if me ≡ alice then None else Some localhost𝕊
      port ← map HS.fromIntegral $ fromSomeCxt $ portMap ⋕? alice
      net ← io $ netIOCreate addr port
      sh  ← io $ setup_semi_honest_c net (serializePrin me ρvsC)
      let sess = EMPSession { channelES = net , semiHonestES = sh }
      modifyL iStateSessionsYaoL ((them ↦ sess) ⩌!)
      return sess
    Some sess → return sess
  where portYao = HS.fromIntegral 12345
        alice   = getAlice ρvsC

getSession ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m) ⇒ 𝑃 PrinVal → m EMPSession
getSession ρvsC = do
  me   ← whoAmI
  them ← getOther me ρvsC
  sessions ← getL iStateSessionsYaoL
  fromSomeCxt $ sessions ⋕? them

yaoShare ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadIO m) ⇒ SemiHonest → HS.Int → BaseVal → m EMPVal
yaoShare sh ρvFr = \case
  BoolBV b   → map BoolEV $ io $ empShareBit sh ρvFr b
  NatBV pr n → do
    prec ← serializePrec pr
    map (NatEV pr) $ io $ empShareInt sh ρvFr prec (HS.fromIntegral n)
  IntBV pr z → do
    prec ← serializePrec pr
    map (IntEV pr) $ io $ empShareInt sh ρvFr prec z
  FltBV pr f → throwIErrorCxt NotImplementedIError "[Yao] yaoShare: 𝔻 (Float) not implemented" empty𝐿

yaoReveal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadIO m) ⇒ SemiHonest → HS.Int → 𝑃 PrinVal → MPCVal 'Yao2P → m Val
yaoReveal sh ρvTo ρvsTo = \case
  BaseMV (BoolEV eb)   → map (BaseV ∘ BoolBV) $ io $ empBitReveal sh ρvTo eb
  BaseMV (IntEV pr ez) → map (BaseV ∘ (IntBV pr) ∘ (trPrInt pr) ∘ HS.fromIntegral) $ io $ empIntegerReveal sh ρvTo ez
  BaseMV (NatEV pr en) → map (BaseV ∘ (NatBV pr) ∘ (trPrNat pr) ∘ HS.fromIntegral) $ io $ empIntegerReveal sh ρvTo en
  PairMV v̂₁ v̂₂ → do
    v₁ ← yaoReveal sh ρvTo ρvsTo v̂₁
    v₂ ← yaoReveal sh ρvTo ρvsTo v̂₂
    return $ PairV (toValP v₁) (toValP v₂)
  v̂ → throwIErrorCxt NotImplementedIError "comin up soon boss" $ frhs [ ("v̂", pretty v̂) ]
  where toValP = SSecVP (SecM ρvsTo)

instance Protocol 'Yao2P where
  type ProtocolVal 'Yao2P = EMPVal

  typeOf ∷ P 'Yao2P → EMPVal → BaseType
  typeOf _p = empType

  shareBaseVal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'Yao2P → PrinVal → 𝑃 PrinVal → BaseVal → m EMPVal
  shareBaseVal _p ρvFr ρvsTo bv = do
    yaoCheck ρvFr ρvsTo
    sh ← map semiHonestES $ handleSession ρvsTo
    yaoShare sh (serializePrin ρvFr ρvsTo) bv

  shareUnk ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'Yao2P → PrinVal → 𝑃 PrinVal → BaseType → m EMPVal
  shareUnk p ρvFr ρvsTo bτ = do
    yaoCheck ρvFr ρvsTo
    sh ← map semiHonestES $ handleSession ρvsTo
    yaoShare sh (serializePrin ρvFr ρvsTo) (defaultBaseValOf bτ)

  embedBaseVal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'Yao2P → 𝑃 PrinVal → BaseVal → m EMPVal
  embedBaseVal _p ρvsFrTo bv = do
    yaoCheck2P ρvsFrTo
    sh ← map semiHonestES $ getSession ρvsFrTo
    yaoShare sh public bv
    where public = HS.fromIntegral 0

  exePrim ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'Yao2P → 𝑃 PrinVal → Op → 𝐿 EMPVal → m EMPVal
  exePrim _p ρvsC op evs = do
    yaoCheck2P ρvsC
    sh ← map semiHonestES $ getSession ρvsC
    case (op, tohs evs) of
      (NotO, [ BoolEV eb₁ ]) → map BoolEV $ io $ empBitNot sh eb₁
      (AndO, [ BoolEV eb₁, BoolEV eb₂ ]) → map BoolEV $ io $ empBitAnd sh eb₁ eb₂
      (CondO, [ BoolEV eb₁, BoolEV eb₂, BoolEV eb₃ ]) → map BoolEV $ io $ empBitCond sh eb₁ eb₂ eb₃
      (PlusO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerAdd sh ez₁ ez₂
      (MinusO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerSub sh ez₁ ez₂
      (TimesO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerMult sh ez₁ ez₂
      (DivO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerDiv sh ez₁ ez₂
      (ModO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerMod sh ez₁ ez₂
      (EqO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map BoolEV $ io $ empIntegerEq sh ez₁ ez₂
      (LTO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map BoolEV $ io $ empIntegerLt sh ez₁ ez₂
      (GTO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ]) | pr₁ ≡ pr₂ → map BoolEV $ io $ empIntegerGt sh ez₁ ez₂
      (CondO, [ BoolEV eb₁, IntEV pr₁ ez₁, IntEV pr₂ ez₂]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerCond sh eb₁ ez₁ ez₂
      (PlusO, [ NatEV pr₁ en₁, NatEV pr₂ en₂ ]) | pr₁ ≡ pr₂ → map (NatEV pr₁) $ io $ empIntegerAdd sh en₁ en₂
      (EqO, [ NatEV pr₁ en₁, NatEV pr₂ en₂ ]) | pr₁ ≡ pr₂ → map BoolEV $ io $ empIntegerEq sh en₁ en₂
      (CondO, [ BoolEV eb₁, NatEV pr₁ en₁, NatEV pr₂ en₂]) | pr₁ ≡ pr₂ → map (NatEV pr₁) $ io $ empIntegerCond sh eb₁ en₁ en₂
      _ → throwIErrorCxt NotImplementedIError "comin up soon boss" $ frhs [ ("op", pretty op), ("evs", pretty evs) ]

  reveal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'Yao2P → 𝑃 PrinVal → PrinVal → MPCVal 'Yao2P → m Val
  reveal p ρvsFr ρvTo v̂ = do
    yaoCheck ρvTo ρvsFr
    sh ← map semiHonestES $ getSession ρvsFr
    v ← yaoReveal sh (serializePrin ρvTo ρvsFr) (single𝑃 ρvTo) v̂
    me ← whoAmI
    return $ if me ≡ ρvTo then v else UnknownV
