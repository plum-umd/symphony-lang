module Allyn.Interpreter.Yao where

import UVMHS
import AddToUVMHS

import Allyn.Syntax
import Allyn.Interpreter.Types
import Allyn.Interpreter.Dist.Types
import Allyn.Interpreter.BaseVal
import Allyn.Interpreter.Pretty ()
import Allyn.Interpreter.Lens
import Allyn.Interpreter.Error
import Allyn.Interpreter.Truncating

import Allyn.Interpreter.EMP
import Allyn.Interpreter.Send

import qualified Prelude as HS

yaoCheck2P ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m) ⇒ 𝑃 PrinVal → m ()
yaoCheck2P ρvsC = do
  guardErr (count ρvsC ≡ 2) $
    throwIErrorCxt TypeIError "yaoCheck2P: count ρvsC ≢ 2" $ frhs
    [ ("ρvsC", pretty ρvsC)
    ]

yaoCheckShareReveal ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m) ⇒ PrinVal → 𝑃 PrinVal → m ()
yaoCheckShareReveal ρv ρvsC = do
  yaoCheck2P ρvsC
  guardErr (ρv ∈ ρvsC) $
    throwIErrorCxt TypeIError "yaoCheckShareReveal: ρv ∉ ρvsC" $ frhs
    [ ("ρv", pretty ρv)
    , ("ρvsC", pretty ρvsC)
    ]

empPrec ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m) ⇒ IPrecision → m HS.Int
empPrec = \case
  FixedIPr n m → return $ HS.fromIntegral $ n + m
  pr → throwIErrorCxt NotImplementedIError "[Yao] serializePrec: precision pr not supported" $ frhs [ ("pr", pretty pr) ]

empPrin ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m) ⇒ PrinVal → 𝑃 PrinVal → m ℕ
empPrin ρv ρvsC = do
  empIds ← fromSomeCxt $ map (dict𝐼 ∘ iter) $ zipSameLength (list ρvsC) (frhs [1..(count ρvsC)])
  fromSomeCxt $ empIds ⋕? ρv

empPublic ∷ HS.Int
empPublic = HS.fromIntegral 0

mkSession ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m, STACK) ⇒ 𝔹 → 𝑃 PrinVal → m EMPProtocol
mkSession isPlain ρvsC = do
  ρvMe   ← fromSomeCxt *$ askL iCxtMeL
  ρvThem ← fromSomeCxt $ view one𝑃L $ ρvsC ∖ (single𝑃 ρvMe)
  ep ← if isPlain then
         io $ plainCreate
       else do
         ch ← getOrMkChannel ρvMe ρvThem
         prin ← empPrin ρvMe ρvsC
         io $ semiHonestCreate ch (HS.fromIntegral prin)
  modifyL iStateSessionsYaoL ((ρvThem ↦ ep) ⩌!)
  return ep

getSession ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m, STACK) ⇒ 𝑃 PrinVal → m (𝑂 EMPProtocol)
getSession ρvsC = do
  ρvMe   ← fromSomeCxt *$ askL iCxtMeL
  ρvThem ← fromSomeCxt $ view one𝑃L $ ρvsC ∖ (single𝑃 ρvMe)
  sessions ← getL iStateSessionsYaoL
  return $ sessions ⋕? ρvThem

getOrMkSession ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m, STACK) ⇒ 𝔹 → 𝑃 PrinVal → m EMPProtocol
getOrMkSession isPlain ρvsC = do
  ep𝑂 ← getSession ρvsC
  case ep𝑂 of
    None    → mkSession isPlain ρvsC
    Some ep → return ep

-------------
--- Share ---
-------------

empShare ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadIO m) ⇒ EMPProtocol → HS.Int → ClearBaseVal → m EMPVal
empShare ep ρvFr = \case
  BulV → todoCxt
  BoolV b   → map BoolEV $ io $ empShareBit ep ρvFr b
  NatV pr n → do
    prec ← empPrec pr
    map (NatEV pr) $ io $ empShareInt ep ρvFr prec (HS.fromIntegral n)
  IntV pr z → do
    prec ← empPrec pr
    map (IntEV pr) $ io $ empShareInt ep ρvFr prec z
  FltV _pr _f → todoCxt
  StrV _s → todoCxt
  PrinV _ρv → todoCxt
  PrinSetV _ρvs → todoCxt

mpcOrPlainShare ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m) ⇒ 𝔹 → PrinVal → 𝑃 PrinVal → (ClearBaseVal ∨ BaseType) → m EMPVal
mpcOrPlainShare isPlain ρvFr ρvsTo cbvorbτ = do
  yaoCheckShareReveal ρvFr ρvsTo
  ep ← getOrMkSession isPlain ρvsTo
  bvc ← case isPlain of
          True  → commClearBaseVal ρvFr ρvsTo cbvorbτ
          False → elimChoice return (return ∘ defaultClearBaseVal) cbvorbτ
  prin ← empPrin ρvFr ρvsTo
  empShare ep (HS.fromIntegral prin) bvc

yaoShare ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m) ⇒ PrinVal → 𝑃 PrinVal → (ClearBaseVal ∨ BaseType) → m EMPVal
yaoShare = mpcOrPlainShare False

plainShare ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m) ⇒ PrinVal → 𝑃 PrinVal → (ClearBaseVal ∨ BaseType) → m EMPVal
plainShare = mpcOrPlainShare True

-------------
--- Embed ---
-------------

yaoOrPlainEmbed ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m) ⇒ 𝔹 → 𝑃 PrinVal → ClearBaseVal → m EMPVal
yaoOrPlainEmbed isPlain ρvsFrTo bv = do
  yaoCheck2P ρvsFrTo
  ep ← getOrMkSession isPlain ρvsFrTo
  empShare ep empPublic bv

yaoEmbed ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m) ⇒ 𝑃 PrinVal → ClearBaseVal → m EMPVal
yaoEmbed = yaoOrPlainEmbed False

plainEmbed ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m) ⇒ 𝑃 PrinVal → ClearBaseVal → m EMPVal
plainEmbed = yaoOrPlainEmbed True

------------
--- Prim ---
------------

yaoPrim ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m) ⇒ 𝑃 PrinVal → Op → 𝐿 EMPVal → m EMPVal
yaoPrim ρvsC op evs = do
  yaoCheck2P ρvsC
  ep ← fromSomeCxt *$ getSession ρvsC
  case (op, tohs evs) of
    (NotO,   [ BoolEV eb₁ ])                                             → map BoolEV      $ io $ empBitNot ep eb₁
    (AndO,   [ BoolEV eb₁,    BoolEV eb₂ ])                              → map BoolEV      $ io $ empBitAnd ep eb₁ eb₂
    (PlusO,  [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ])               | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerAdd ep ez₁ ez₂
    (MinusO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ])               | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerSub ep ez₁ ez₂
    (TimesO, [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ])               | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerMult ep ez₁ ez₂
    (DivO,   [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ])               | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerDiv ep ez₁ ez₂
    (ModO,   [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ])               | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerMod ep ez₁ ez₂
    (EqO,    [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ])               | pr₁ ≡ pr₂ → map BoolEV      $ io $ empIntegerEq ep ez₁ ez₂
    (LTEO,   [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ])               | pr₁ ≡ pr₂ → map BoolEV      $ io $ empIntegerLte ep ez₁ ez₂
    (LTO,    [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ])               | pr₁ ≡ pr₂ → map BoolEV      $ io $ empIntegerLt ep ez₁ ez₂
    (GTO,    [ IntEV pr₁ ez₁, IntEV pr₂ ez₂ ])               | pr₁ ≡ pr₂ → map BoolEV      $ io $ empIntegerGt ep ez₁ ez₂
    (PlusO,  [ NatEV pr₁ en₁, NatEV pr₂ en₂ ])               | pr₁ ≡ pr₂ → map (NatEV pr₁) $ io $ empIntegerAdd ep en₁ en₂
    (EqO,    [ NatEV pr₁ en₁, NatEV pr₂ en₂ ])               | pr₁ ≡ pr₂ → map BoolEV      $ io $ empIntegerEq ep en₁ en₂
    (LTEO,   [ NatEV pr₁ en₁, NatEV pr₂ en₂ ])               | pr₁ ≡ pr₂ → map BoolEV      $ io $ empIntegerLte ep en₁ en₂
    (GTO,    [ NatEV pr₁ ez₁, NatEV pr₂ ez₂ ])               | pr₁ ≡ pr₂ → map BoolEV      $ io $ empIntegerGt ep ez₁ ez₂
    (CondO,  [ BoolEV eb₁,    BoolEV eb₂,    BoolEV eb₃ ])               → map BoolEV      $ io $ empBitCond ep eb₁ eb₂ eb₃
    (CondO,  [ BoolEV eb₁,    IntEV pr₁ ez₁, IntEV pr₂ ez₂]) | pr₁ ≡ pr₂ → map (IntEV pr₁) $ io $ empIntegerCond ep eb₁ ez₁ ez₂
    (CondO,  [ BoolEV eb₁,    NatEV pr₁ en₁, NatEV pr₂ en₂]) | pr₁ ≡ pr₂ → map (NatEV pr₁) $ io $ empIntegerCond ep eb₁ en₁ en₂
    _ → throwIErrorCxt NotImplementedIError "comin up soon boss" $ frhs [ ("op", pretty op), ("evs", pretty evs) ]

--------------
--- Reveal ---
--------------

empReveal ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadIO m) ⇒ EMPProtocol → HS.Int → EMPVal → m ClearBaseVal
empReveal ep ρvTo = \case
  BoolEV eb   → map BoolV                                        $ io $ empBitReveal     ep ρvTo eb
  IntEV pr ez → map ((IntV pr) ∘ (trPrInt pr) ∘ HS.fromIntegral) $ io $ empIntegerReveal ep ρvTo ez
  NatEV pr en → map ((NatV pr) ∘ (trPrNat pr) ∘ HS.fromIntegral) $ io $ empIntegerReveal ep ρvTo en
  v̂ → throwIErrorCxt NotImplementedIError "comin up soon boss" $ frhs [ ("v̂", pretty v̂) ]

yaoReveal ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m) ⇒ 𝑃 PrinVal → PrinVal → EMPVal → m ClearBaseVal
yaoReveal ρvsFr ρvTo ev = do
  yaoCheckShareReveal ρvTo ρvsFr
  ep ← fromSomeCxt *$ getSession ρvsFr
  prin ← empPrin ρvTo ρvsFr
  empReveal ep (HS.fromIntegral prin) ev

instance Protocol 'Yao2P where
  type Share 'Yao2P = EMPVal

  share ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m) ⇒ P 'Yao2P → PrinVal → 𝑃 PrinVal → (ClearBaseVal ∨ BaseType) → m EMPVal
  share _p = yaoShare

  embed ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m) ⇒ P 'Yao2P → 𝑃 PrinVal → ClearBaseVal → m EMPVal
  embed _p = yaoEmbed

  prim ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m) ⇒ P 'Yao2P → 𝑃 PrinVal → Op → 𝐿 EMPVal → m EMPVal
  prim _p = yaoPrim

  reveal ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m) ⇒ P 'Yao2P → 𝑃 PrinVal → PrinVal → EMPVal → m ClearBaseVal
  reveal _p = yaoReveal

instance Protocol 'YaoPlainP where
  type Share 'YaoPlainP = EMPVal

  share ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m) ⇒ P 'YaoPlainP → PrinVal → 𝑃 PrinVal → (ClearBaseVal ∨ BaseType) → m EMPVal
  share _p = plainShare

  embed ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m) ⇒ P 'YaoPlainP → 𝑃 PrinVal → ClearBaseVal → m EMPVal
  embed _p = plainEmbed

  prim ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m) ⇒ P 'YaoPlainP → 𝑃 PrinVal → Op → 𝐿 EMPVal → m EMPVal
  prim _p = yaoPrim

  reveal ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, MonadState (IState v) m, MonadIO m) ⇒ P 'YaoPlainP → 𝑃 PrinVal → PrinVal → EMPVal → m ClearBaseVal
  reveal _p = yaoReveal
