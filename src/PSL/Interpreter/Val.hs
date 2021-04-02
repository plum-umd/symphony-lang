module PSL.Interpreter.Val where

import UVMHS
import AddToUVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Lens
import PSL.Interpreter.Error
import PSL.Interpreter.Share

import PSL.Interpreter.Primitives

import qualified Prelude as HS

--------------------
--- Public Stuff ---
--------------------

introValP ∷ (STACK) ⇒ Val → IM ValP
introValP v = do
  gm ← askL iCxtGlobalModeL
  return $ SSecVP gm v

elimValP ∷ (STACK) ⇒ ValP → IM Val
elimValP ṽ = do
  v̑ ← unValP ṽ
  elimValS v̑

restrictValP ∷ (STACK) ⇒ ValP → IM ValP
restrictValP ṽ = do
  gm ← askL iCxtGlobalModeL
  case gm of
    TopM     → return ṽ
    SecM ρvs → case ṽ of
      SSecVP m v → return ∘ SSecVP (gm ⊓ m) *$ recVal v
      ISecVP b   → return ∘ ISecVP *$ mapM recVal (restrict ρvs b)
      ShareVP φ ρvs' v̂ → do
        guardErr (ρvs ≡ ρvs') $
          throwIErrorCxt TypeIError "restrictValP: ρvs ≢ ρvs'" $ frhs
          [ ("ρvs", pretty ρvs)
          , ("ρvs'", pretty ρvs')
          ]
        return $ ShareVP φ ρvs' v̂
    where recVal v = case v of
            BaseV _ → return v
            StrV _ → return v
            BulV → return v
            LV ṽ' → do
              ṽ'' ← restrictValP ṽ'
              return $ LV ṽ''
            RV ṽ' → do
              ṽ'' ← restrictValP ṽ'
              return $ RV ṽ''
            NilV → return v
            ConsV ṽ₁ ṽ₂ → do
              ṽ₁' ← restrictValP ṽ₁
              ṽ₂' ← restrictValP ṽ₂
              return $ ConsV ṽ₁' ṽ₂'
            CloV _ _ _ _  → return v
            TCloV _ _ _ → return v
            PrinV _ → return v
            PrinSetV _ → return v
            LocV _ _ → return v
            ArrayV ṽs → ArrayV ∘ spvec𝐼 ^$ mapMOn (iter ṽs) (mapMSnd restrictValP)
            PairV ṽ₁ ṽ₂ → do
              ṽ₁' ← restrictValP ṽ₁
              ṽ₂' ← restrictValP ṽ₂
              return $ PairV ṽ₁' ṽ₂'
            UnknownV _ → return v
            DefaultV → return DefaultV

modeFrValP ∷ (STACK) ⇒ ValP → Mode
modeFrValP = \case
  SSecVP m _ → m
  ISecVP b → SecM $ keys b
  ShareVP _ ρvs _ → SecM $ ρvs

shareValP ∷ (STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → PrinVal → ValP → IM ValP
shareValP p φ ρvs ρv ṽ = shareOrEmbedValP p φ ρvs (Some ρv) ṽ

embedValP ∷ (STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → ValP → IM ValP
embedValP p φ ρvs ṽ = shareOrEmbedValP p φ ρvs None ṽ

revealValP ∷ (STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → 𝑃 PrinVal → ValP → IM ValP
revealValP p φ ρvs ρvsRevealees ṽ = map (SSecVP (SecM ρvsRevealees)) $ revealValOrMPCVal p φ ρvs ρvsRevealees *$ unValS φ ρvs *$ unValP ṽ

viewPairValP ∷ (STACK) ⇒ ValP → FailT IM (ValP ∧ ValP)
viewPairValP ṽ = do
  v̑ ← lift $ unValP ṽ
  case v̑ of
    SSecVS (PairV ṽ₁ ṽ₂) → return $ ṽ₁ :* ṽ₂
    ShareVS φ ρvs (PairMV v̂₁ v̂₂) → return $ ShareVP φ ρvs v̂₁ :* ShareVP φ ρvs v̂₂
    _ → abort

viewSumValP ∷ (STACK) ⇒ ValP → FailT IM (ValP ∧ ValP ∧ ValP)
viewSumValP ṽ = do
  v̑ ← lift $ unValP ṽ
  case v̑ of
    SSecVS (LV ṽ₂) → do
      ṽ₁ ← lift $ introValP $ BaseV $ BoolBV True
      ṽ₃ ← lift $ introValP DefaultV
      return $ ṽ₁ :* ṽ₂ :* ṽ₃
    SSecVS (RV ṽ₃) → do
      ṽ₁ ← lift $ introValP $ BaseV $ BoolBV False
      ṽ₂ ← lift $ introValP DefaultV
      return $ ṽ₁ :* ṽ₂ :* ṽ₃
    ShareVS φ ρvs (SumMV pv₁ v̂₂ v̂₃) → return $ ShareVP φ ρvs (BaseMV pv₁) :* ShareVP φ ρvs v̂₂ :* ShareVP φ ρvs v̂₃
    _ → abort

viewNilValP ∷ (STACK) ⇒ ValP → FailT IM ()
viewNilValP ṽ = do
  v̑ ← lift $ unValP ṽ
  case v̑ of
    SSecVS NilV → return ()
    _ → abort

viewConsValP ∷ (STACK) ⇒ ValP → FailT IM (ValP ∧ ValP)
viewConsValP ṽ = do
  v̑ ← lift $ unValP ṽ
  case v̑ of
    SSecVS (ConsV ṽ₁ ṽ₂) → return $ ṽ₁ :* ṽ₂
    _ → abort

notValP ∷ (STACK) ⇒ ValP → IM ValP
notValP ṽ = primValP NotO $ frhs [ ṽ ]

primValP ∷ (STACK) ⇒ Op → 𝐿 ValP → IM ValP
primValP op = withShareInfo (primVals op) (primMPCVals op)

muxValP ∷ (STACK) ⇒ ValP → ValP → ValP → IM ValP
muxValP ṽ₁ ṽ₂ ṽ₃ = undefined -- TODO

sumValP ∷ (STACK) ⇒ ValP → ValP → IM ValP
sumValP ṽ₁ ṽ₂ = undefined -- TODO

introLocV ∷ (STACK) ⇒ ℤ64 → IM Val
introLocV ℓ = do
  m ← askL iCxtGlobalModeL
  return $ LocV m ℓ

elimLocV ∷ (STACK) ⇒ Val → IM ℤ64
elimLocV v = do
  m ← askL iCxtGlobalModeL
  case v of
    LocV m' ℓ → do
      guardErr (m ≡ m') $
        throwIErrorCxt TypeIError "elimLocV: m ≠ m'" $ frhs
          [ ("m",pretty m)
          , ("m'",pretty m')
          ]
      return ℓ
    _ → throwIErrorCxt TypeIError "elimLocV: v ≠ LocV _ _" $ frhs
          [ ("v",pretty v) ]

-------------
--- Other ---
-------------

unValP ∷ (STACK) ⇒ ValP → IM ValS
unValP ṽ = do
  gm ← askL iCxtGlobalModeL
  case ṽ of
    SSecVP m v → do
      -- (1) All parties executing this code must have the value (gm ⊑ m)
      guardErr (gm ⊑ m) $
        throwIErrorCxt TypeIError "unValP: SSecVP: gm ⋢ m " $ frhs
        [ ("gm",pretty gm)
        , ("m",pretty m)
        ]
      return $ SSecVS v
    ShareVP φ ρvs v̂ → do
      -- (1) All parties executing this code must have the value (gm ⊑ SecM ρvs) AND
      -- (2) All parties that have the value (i.e. the parties amongst whom the value is shared) must be executing this code (SecM ρvs ⊑ gm)
      guardErr (gm ≡ SecM ρvs) $
        throwIErrorCxt TypeIError "unValP: gm ≢ SecM ρvs" $ frhs
        [ ("gm", pretty gm)
        , ("ρvs", pretty ρvs)
        ]
      return $ ShareVS φ ρvs v̂
    _ → throwIErrorCxt TypeIError "withValP: ṽ ∉ {SSecVP _ _,ShareVP _ _ _}" $ frhs
        [ ("ṽ",pretty ṽ) ]

reValP ∷ (STACK) ⇒ ValS → IM ValP
reValP = \case
  SSecVS v → introValP v
  ShareVS φ ρvs v̂ → case v̂ of
    DefaultMV → return $ SSecVP (SecM ρvs) DefaultV
    BulMV → return $ SSecVP (SecM ρvs) BulV
    BaseMV pv → return $ ShareVP φ ρvs v̂
    PairMV v̂₁ v̂₂ → do
      ṽ₁ ← reValP $ ShareVS φ ρvs v̂₁
      ṽ₂ ← reValP $ ShareVS φ ρvs v̂₂
      return $ SSecVP (SecM ρvs) $ PairV ṽ₁ ṽ₂
    SumMV pv₁ v̂₂ v̂₃ → return $ ShareVP φ ρvs v̂


unValS ∷ (STACK) ⇒ SProt p → 𝑃 PrinVal → ValS → IM (Val ∨ MPCVal p)
unValS φ ρvs = \case
  SSecVS v          → return $ Inl v
  ShareVS φ' ρvs' v̂ → case deq φ φ' of
    NoDEq  → throwIErrorCxt TypeIError "bad" $ empty𝐿
    YesDEq → do
      guardErr (ρvs ≡ ρvs') $
        throwIErrorCxt TypeIError "bad" $ empty𝐿
      return $ Inr v̂

reValS ∷ (STACK, Protocol p) ⇒ SProt p → 𝑃 PrinVal → (Val ∨ MPCVal p) → ValS
reValS φ ρvs = \case
  Inl v → SSecVS v
  Inr v̂ → ShareVS φ ρvs v̂

elimValS ∷ (STACK) ⇒ ValS → IM Val
elimValS = \case
  SSecVS v → return v
  v̑        → do
    ṽ ← reValP v̑
    throwIErrorCxt TypeIError "elimValS: ṽ ≢ SSecVP _" $ frhs [ ("ṽ", pretty ṽ) ]

shareInfoFrValSs ∷ (STACK) ⇒ 𝐿 ValS → 𝑂 (Prot ∧ 𝑃 PrinVal)
shareInfoFrValSs v̑s = foldFromOn None v̑s $ \ v̑ si → case (si, v̑) of
                                                      (None, SSecVS _)        → None
                                                      (None, ShareVS φ ρvs _) → Some $ (protFrSProt φ) :* ρvs
                                                      (Some _, _)             → si

shareOrEmbedValP ∷ (STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → 𝑂 PrinVal → ValP → IM ValP
shareOrEmbedValP p φ ρvs oρv ṽ = reValP *$ map (reValS φ ρvs) $ map Inr $ shareOrEmbed p φ ρvs oρv *$ unValS φ ρvs *$ unValP ṽ

shareOrEmbed ∷ (STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → 𝑂 PrinVal → (Val ∨ MPCVal p) → IM (MPCVal p)
shareOrEmbed p φ ρvs oρv vorv̂ = case vorv̂ of
  Inl v → case v of
    DefaultV → return DefaultMV
    BulV     → return BulMV
    BaseV bv → map BaseMV $ case oρv of
      None    → embedBaseVal p ρvs bv
      Some ρv → shareBaseVal p ρvs ρv bv
    PairV ṽ₁ ṽ₂ → do
      v̂₁ ← shareOrEmbedR *$ unValSR *$ unValP ṽ₁
      v̂₂ ← shareOrEmbedR *$ unValSR *$ unValP ṽ₂
      return $ PairMV v̂₁ v̂₂
    LV ṽ → do
      v̂  ← shareOrEmbedR *$ unValSR *$ unValP ṽ
      tt ← embedBaseVal p ρvs $ BoolBV True
      return $ SumMV tt v̂ DefaultMV
    RV ṽ → do
      v̂  ← shareOrEmbedR *$ unValSR *$ unValP ṽ
      ff ← embedBaseVal p ρvs $ BoolBV False
      return $ SumMV ff DefaultMV v̂
    UnknownV τ → do
      ρv ← error𝑂 oρv $ throwIErrorCxt TypeIError "shareOrEmbedVal: unknown of type τ cannot be embedded" $ frhs [ ("τ", pretty τ) ]
      shareUnknown p ρvs ρv τ
    _ → throwIErrorCxt TypeIError "shareOrEmbedVal: value v cannot be shared or embedded" $ frhs [ ("v", pretty v) ]
  Inr v̂ → return v̂
  where shareOrEmbedR = shareOrEmbed p φ ρvs oρv
        unValSR       = unValS φ ρvs

shareUnknown ∷ (STACK, Protocol p) ⇒ P p → 𝑃 PrinVal → PrinVal → Type → IM (MPCVal p)
shareUnknown p ρvs ρv τ = case τ of
  UnitT → return BulMV
  BaseT bτ → do
    pv ← shareUnk p ρvs ρv bτ
    return $ BaseMV pv
  τ₁ :×: τ₂ → do
    v̂₁ ← shareUnknownR τ₁
    v̂₂ ← shareUnknownR τ₂
    return $ PairMV v̂₁ v̂₂
  τ₁ :+: τ₂ → do
    tag ← shareUnk p ρvs ρv 𝔹T
    v̂₁ ← shareUnknownR τ₁
    v̂₂ ← shareUnknownR τ₂
    return $ SumMV tag v̂₁ v̂₂
  _ → throwIErrorCxt TypeIError "shareUnknown: unknown of type τ cannot be shared" $ frhs [ ("τ", pretty τ) ]
  where shareUnknownR = shareUnknown p ρvs ρv

revealValOrMPCVal ∷ (STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → 𝑃 PrinVal → (Val ∨ MPCVal p) → IM Val
revealValOrMPCVal p φ ρvs ρvsRevealees = \case
  Inl v → revealVal p φ ρvs ρvsRevealees v
  Inr v̂ → reveal p ρvs ρvsRevealees v̂

revealVal ∷ (STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → 𝑃 PrinVal → Val → IM Val
revealVal p φ ρvs ρvsRevealees v = case v of
  DefaultV  → return v
  BulV      → return v
  BaseV _bv → return v
  PairV ṽ₁ ṽ₂ → do
    ṽ₁ʳ ← revealValPR ṽ₁
    ṽ₂ʳ ← revealValPR ṽ₂
    return $ PairV ṽ₁ʳ ṽ₂ʳ
  LV ṽ → do
    ṽʳ ← revealValPR ṽ
    return $ LV ṽʳ
  RV ṽ → do
    ṽʳ ← revealValPR ṽ
    return $ RV ṽʳ
  NilV → return v
  ConsV ṽ₁ ṽ₂ → do
    ṽ₁ʳ ← revealValPR ṽ₁
    ṽ₂ʳ ← revealValPR ṽ₂
    return $ ConsV ṽ₁ʳ ṽ₂ʳ
  _ → throwIErrorCxt NotImplementedIError "revealVal: revealing value v unimplemented" $ frhs
      [ ("v", pretty v)
      ]
  where revealValPR = revealValP p φ ρvs ρvsRevealees

withShareInfo ∷ (STACK) ⇒ (𝐿 Val → IM a) → (∀ p. (Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → 𝐿 (MPCVal p) → IM a) → 𝐿 ValP → IM a
withShareInfo kVals kMPCVals ṽs = do
  v̑s ← mapM unValP ṽs
  let osi = shareInfoFrValSs v̑s
  case osi of
    None → do
      vs ← mapM elimValS v̑s
      kVals vs
    Some (prot :* ρvs) →
      withProt prot $ \ p φ → do
      vorv̂s ← mapM (unValS φ ρvs) v̑s
      v̂s ← mapM (shareOrEmbed p φ ρvs None) vorv̂s
      kMPCVals p φ ρvs v̂s

primVals ∷ (STACK) ⇒ Op → 𝐿 Val → IM ValP
primVals op vs = do
  bvs ← error𝑂 (mapM (view baseVL) vs) (throwIErrorCxt TypeIError "primValP: mapM (view baseVL) vs ≡ None" $ frhs
                                        [ ("vs", pretty vs)
                                        ])
  bv' ← interpPrim op bvs
  introValP $ BaseV bv'

primMPCVals ∷ (STACK, Protocol p) ⇒ Op → P p → SProt p → 𝑃 PrinVal → 𝐿 (MPCVal p) → IM ValP
primMPCVals op p φ ρvs v̂s = do
  pvs ← error𝑂 (mapM (view baseMVL) v̂s) (throwIErrorCxt TypeIError "primValP: mapM (view baseMVL) v̂s ≡ None" $ frhs
                                         [ ("v̂s", pretty v̂s)
                                         ])
  pv' ← exePrim p ρvs op pvs
  return $ ShareVP φ ρvs $ BaseMV pv'

------------------------------------
--- Intro and Elim on Non-Shares ---
------------------------------------



------------------------------
--- Share / Embed / Reveal ---
------------------------------


{-




----------------
--- UnShares ---
----------------

withShareInfo ∷ 𝐿 UnShare → (∀ p. (Protocol p)

--valToMPC ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ Val → ReaderT (MPCify p) IM (MPCVal p)
shareInfoFrUnShare ∷ UnShare → ShareInfo
shareInfoFrUnShare = \case
  NotShared _v       → NotShare
  Shared p sp ρvs _v̂ → Share p sp ρvs

joinShareInfo ∷ ShareInfo → ShareInfo → IM ShareInfo
joinShareInfo si₁ si₂ = case (si₁, si₂) of
  (NotShare, _) → return si₂
  (_, NotShare) → return si₁
  (Share _ _ _, Share _ _ _) →
    if si₁ ≡ si₂ then
      return si₁
    else
      throwIErrorCxt TypeIError "joinShareInfo: si₁ ≢ si₂" $ frhs
      [ ("si₁", pretty si₁)
      , ("si₂", pretty si₂)
      ]

shareInfoFrUnShares ∷ 𝐿 UnShare → IM ShareInfo
shareInfoFrUnShares uss = mfold NotShare joinShareInfo $ map shareInfoFrUnShare uss

withUnShares ∷ (𝐿 Val → IM a) → (∀ p. (Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → 𝐿 (MPCVal p) → IM a) → 𝐿 UnShare → IM a
withUnShares uss kVals kMPCVals = do
  si ← shareInfoFrUnShares uss
  case si of
    NotShare → do
      vs ← valsFrUnShares
      kVals vs
    Share p sp ρvs → do
      v̂s ← mpcValsFrUnShares p sp ρvs
      kMPCVals p sp ρvs v̂s
  where valsFrUnShares = mapM valFrUnShare uss
        valFrUnShare us = fromSome (view notSharedL us)
        mpcValsFrUnShares p sp ρvs = mapM (mpcValFrUnShare p sp ρvs) uss
        mpcValFrUnShare p sp₁ ρvs₁ = \case
          NotShared v          → runReaderT (MPCify { proxyMPC = p, protMPC = sp₁, fromMPC = None, toMPC = ρvs₁ }) $ valToMPC v
          Shared _p sp₂ ρvs₂ v̂ →
            case deq sp₁ sp₂ of
              NoDEq  → impossibleM
              YesDEq → return v̂

primValP ∷ Op → 𝐿 ValP → IM ValP
primValP op ṽs = reValP *$ primValS op *$ mapM unValP ṽs

primUnShare ∷ Op → 𝐿 UnShare → IM UnShare
primUnShare op uss = withUnShares kPrimVals kPrimMPCVals uss
  where kPrimVals vs = do
          bvs ← error𝑂 (mapMOn vs $ view baseVL) (throwIErrorCxt TypeIError "primUnShare: mapMOn vs $ view baseVL ≡ None" $ frhs
                                                  [ ("vs", pretty vs)
                                                  ])
          bv' ← interpPrim op bvs
          return $ NotShared $ BaseV bv'
        kPrimMPCVals p sp ρvs v̂s = do
          pvs ← error𝑂 (mapMOn v̂s $ view baseMVL) (throwIErrorCxt TypeIError "primUnShare: mapMOn v̂s $ view baseMVL ≡ None" $ frhs
                                                   [ ("v̂s", pretty v̂s)
                                                   ])
          pv' ← exePrim p ρvs op pvs
          return $ Shared p sp ρvs $ BaseMV pv'

notUnShare ∷ (STACK) ⇒ UnShare → IM UnShare
notUnShare us = primUnShare NotO $ frhs [ us ]

muxUnShare ∷ (STACK) ⇒ UnShare → UnShare → UnShare → IM UnShare
muxUnShare us₁ us₂ us₃ = undefined {-do
  vsorv̂s ← unwrapUnShares $ frhs [ us₁, us₂, us₃ ]
  case vsorv̂s of
    Inl vs → do
      v₁ :* v₂ :* v₃ ← fromSome $ view three𝐿L vs
      bv₁ ← error𝑂 (view baseVL v₁) (throwIErrorCxt TypeIError "muxUnShare: view baseVL v₁ ≡ None" $ frhs
                                    [ ("v₁", pretty v₁)
                                    ])
      v' ← muxVal bv₁ v₂ v₃ -- TODO(ins): check bv₁ : Bool
      return $ NotShared v'
    Inr (ShareInfo p sp ρvs :* v̂s) → do
      v̂₁ :* v̂₂ :* v̂₃ ← fromSome $ view three𝐿L v̂s
      pv₁ ← error𝑂 (view baseMVL v̂₁) (throwIErrorCxt TypeIError "muxUnShare: view baseMVL v̂₁ ≡ None" $ frhs
                                      [ ("v̂₁", pretty v̂₁)
                                      ])
      v̂' ← muxMPCVal p ρvs pv₁ v̂₂ v̂₃ -- TODO(ins): check pv₁ : Bool
      return $ Shared p sp ρvs v̂'
    _ → impossibleM-}

muxVal ∷ (STACK) ⇒ BaseVal → Val → Val → IM Val
muxVal bv₁ v₂ v₃ = case (v₂, v₃) of
  (DefaultV, DefaultV) → return DefaultV
  (DefaultV, BaseV bv₃) → do
    let bv₂ = defaultBaseValOf (typeOfBaseVal bv₃)
    bv' ← interpPrim CondO $ frhs [ bv₁, bv₂, bv₃ ]
    return $ BaseV bv'
  (BaseV bv₂, DefaultV) → do
    let bv₃ = defaultBaseValOf (typeOfBaseVal bv₂)
    bv' ← interpPrim CondO $ frhs [ bv₁, bv₂, bv₃ ]
    return $ BaseV bv'
  (BaseV bv₂, BaseV bv₃) → do
    bv' ← interpPrim CondO $ frhs [ bv₁, bv₂, bv₃ ]
    return $ BaseV bv'
  (DefaultV, PairV ṽ₃ₗ ṽ₃ᵣ) → do
    ṽ₂ ← introValP DefaultV
    muxTup ṽ₂ ṽ₂ ṽ₃ₗ ṽ₃ᵣ PairV
  (PairV ṽ₂ₗ ṽ₂ᵣ, DefaultV) → do
    ṽ₃ ← introValP DefaultV
    muxTup ṽ₂ₗ ṽ₂ᵣ ṽ₃ ṽ₃ PairV
  (PairV ṽ₂ₗ ṽ₂ᵣ, PairV ṽ₃ₗ ṽ₃ᵣ) → muxTup ṽ₂ₗ ṽ₂ᵣ ṽ₃ₗ ṽ₃ᵣ PairV
  (DefaultV, LV ṽ₃) → do
    ṽ₂ ← introValP DefaultV
    muxSum False ṽ₂ True ṽ₃
  (LV ṽ₂, DefaultV) → do
    ṽ₃ ← introValP DefaultV
    muxSum True ṽ₂ False ṽ₃
  (DefaultV, RV ṽ₃) → do
    ṽ₂ ← introValP DefaultV
    muxSum False ṽ₂ False ṽ₃
  (RV ṽ₂, DefaultV) → do
    ṽ₃ ← introValP DefaultV
    muxSum False ṽ₂ False ṽ₃
  (LV ṽ₂, LV ṽ₃) → muxSum True ṽ₂ True ṽ₃
  (RV ṽ₂, RV ṽ₃) → muxSum False ṽ₂ False ṽ₃
  (LV ṽ₂, RV ṽ₃) → muxSum True ṽ₂ False ṽ₃
  (RV ṽ₂, LV ṽ₃) → muxSum False ṽ₂ True ṽ₃
  (DefaultV, NilV) → return NilV
  (NilV, DefaultV) → return NilV
  (NilV, NilV) → return NilV
  (DefaultV, ConsV ṽ₃ₗ ṽ₃ᵣ) → do
    ṽ₂ ← introValP DefaultV
    muxTup ṽ₂ ṽ₂ ṽ₃ₗ ṽ₃ᵣ ConsV
  (ConsV ṽ₂ₗ ṽ₂ᵣ, DefaultV) → do
    ṽ₃ ← introValP DefaultV
    muxTup ṽ₂ₗ ṽ₂ᵣ ṽ₃ ṽ₃ ConsV
  (ConsV ṽ₂ₗ ṽ₂ᵣ, ConsV ṽ₃ₗ ṽ₃ᵣ) → muxTup ṽ₂ₗ ṽ₂ᵣ ṽ₃ₗ ṽ₃ᵣ ConsV
  (DefaultV, BulV) → return BulV
  (BulV, DefaultV) → return BulV
  (BulV, BulV) → return BulV
  _ → throwIErrorCxt TypeIError "muxVal: values v₂ and v₃ have different shapes." $ frhs
      [ ("v₂", pretty v₂)
      , ("v₃", pretty v₃)
      ]
  where muxTup ṽ₂ₗ ṽ₂ᵣ ṽ₃ₗ ṽ₃ᵣ constr = do
          ṽ₁ ← introValP $ BaseV bv₁
          us₁ₗ :* us₂ₗ :* us₃ₗ ← (mapM unShareValP $ frhs [ ṽ₁, ṽ₂ₗ, ṽ₃ₗ ]) ≫= fromSome ∘ (view three𝐿L)
          usₗ ← muxUnShare us₁ₗ us₂ₗ us₃ₗ
          ṽₗ ← reShareValP usₗ
          us₁ᵣ :* us₂ᵣ :* us₃ᵣ ← (mapM unShareValP $ frhs [ ṽ₁, ṽ₂ᵣ, ṽ₃ᵣ ]) ≫= fromSome ∘ (view three𝐿L)
          usᵣ ← muxUnShare us₁ᵣ us₂ᵣ us₃ᵣ
          ṽᵣ ← reShareValP usᵣ
          return $ constr ṽₗ ṽᵣ
        muxSum tag₂ ṽ₂ tag₃ ṽ₃ = do
          ṽ₁ ← introValP $ BaseV bv₁
          tag ← (interpPrim CondO $ frhs [ bv₁, BoolBV tag₂, BoolBV tag₃ ]) ≫= fromSome ∘ (view boolBVL)
          us₁ :* us₂ :* us₃ ← (mapM unShareValP $ frhs [ ṽ₁, ṽ₂, ṽ₃ ]) ≫= fromSome ∘ (view three𝐿L)
          us' ← muxUnShare us₁ us₂ us₃
          ṽ' ← reShareValP us'
          return $ if tag then LV ṽ' else RV ṽ'

muxMPCVal ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ P p → 𝑃 PrinVal → (ProtocolVal p) → MPCVal p → MPCVal p → IM (MPCVal p)
muxMPCVal p ρvs pv₁ v̂₂ v̂₃ = case (v̂₂, v̂₃) of
  (DefaultMV, DefaultMV) → return DefaultMV
  (DefaultMV, BulMV) → return BulMV
  (BulMV, DefaultMV) → return BulMV
  (BulMV, BulMV) → return BulMV
  (DefaultMV, BaseMV pv₃) → do
    pv₂ ← embedBaseVal p ρvs (defaultBaseValOf $ typeOf p pv₃)
    pv' ← exePrim p ρvs CondO $ frhs [ pv₁, pv₂, pv₃ ]
    return $ BaseMV pv'
  (BaseMV pv₂, DefaultMV) → do
    pv₃ ← embedBaseVal p ρvs (defaultBaseValOf $ typeOf p pv₂)
    pv' ← exePrim p ρvs CondO $ frhs [ pv₁, pv₂, pv₃ ]
    return $ BaseMV pv'
  (BaseMV pv₂, BaseMV pv₃) → do
    pv' ← exePrim p ρvs CondO $ frhs [ pv₁, pv₂, pv₃ ]
    return $ BaseMV pv'
  (DefaultMV, PairMV v̂₃ₗ v̂₃ᵣ) → muxTup DefaultMV DefaultMV v̂₃ₗ v̂₃ᵣ
  (PairMV v̂₂ₗ v̂₂ᵣ, DefaultMV) → muxTup v̂₂ₗ v̂₂ᵣ DefaultMV DefaultMV
  (PairMV v̂₂ₗ v̂₂ᵣ, PairMV v̂₃ₗ v̂₃ᵣ) → muxTup v̂₂ₗ v̂₂ᵣ v̂₃ₗ v̂₃ᵣ
  (DefaultMV, SumMV pv₃ v̂₃ₗ v̂₃ᵣ) → do
    pv₂ ← embedBaseVal p ρvs (BoolBV False)
    muxSum pv₂ DefaultMV DefaultMV pv₃ v̂₃ₗ v̂₃ᵣ
  (SumMV pv₂ v̂₂ₗ v̂₂ᵣ, DefaultMV) → do
    pv₃ ← embedBaseVal p ρvs (BoolBV False)
    muxSum pv₂ v̂₂ₗ v̂₂ᵣ pv₃ DefaultMV DefaultMV
  (SumMV pv₂ v̂₂ₗ v̂₂ᵣ, SumMV pv₃ v̂₃ₗ v̂₃ᵣ) → muxSum pv₂ v̂₂ₗ v̂₂ᵣ pv₃ v̂₃ₗ v̂₃ᵣ
  _ → throwIErrorCxt TypeIError "muxMPCVal: MPC values v̂₂ and v̂₃ have different shapes." $ frhs
      [ ("v̂₂", pretty v̂₂)
      , ("v̂₃", pretty v̂₃)
      ]
  where muxTup v̂₂ₗ v̂₂ᵣ v̂₃ₗ v̂₃ᵣ = do
          v̂ₗ ← muxMPCVal p ρvs pv₁ v̂₂ₗ v̂₃ₗ
          v̂ᵣ ← muxMPCVal p ρvs pv₁ v̂₂ᵣ v̂₃ᵣ
          return $ PairMV v̂ₗ v̂ᵣ
        muxSum pv₂ v̂₂ₗ v̂₂ᵣ pv₃ v̂₃ₗ v̂₃ᵣ = do
          tag ← exePrim p ρvs CondO $ frhs [ pv₁, pv₂, pv₃ ]
          v̂ₗ ← muxMPCVal p ρvs pv₁ v̂₂ₗ v̂₃ₗ
          v̂ᵣ ← muxMPCVal p ρvs pv₁ v̂₂ᵣ v̂₃ᵣ
          return $ SumMV tag v̂ₗ v̂ᵣ

defaultBaseValOf ∷ BaseType → BaseVal
defaultBaseValOf = \case
  𝔹T → BoolBV False
  ℕT pr → NatBV pr 0
  ℤT pr → IntBV pr $ HS.fromIntegral 0
  𝔽T pr → FltBV pr $ HS.fromIntegral 0

sumUnShare ∷ (STACK) ⇒ UnShare → UnShare → IM UnShare
sumUnShare us₁ us₂ = undefined {- do
  vsorv̂s ← unwrapUnShares $ frhs [ us₁, us₂ ]
  case vsorv̂s of
    Inl vs → do
      v₁ :* v₂ ← fromSome $ view two𝐿L vs
      v' ← sumVal v₁ v₂
      return $ NotShared v'
    Inr (ShareInfo p sp ρvs :* v̂s) → do
      v̂₁ :* v̂₂ ← fromSome $ view two𝐿L v̂s
      v̂' ← sumMPCVal p ρvs v̂₁ v̂₂
      return $ Shared p sp ρvs v̂' -}

sumVal ∷ (STACK) ⇒ Val → Val → IM Val
sumVal v₁ v₂ = case (v₁, v₂) of
  (_, DefaultV) → return v₁
  (DefaultV, _) → return v₂
  (BaseV bv₁, BaseV bv₂) → do
    bv' ← interpPrim PlusO $ frhs [ bv₁, bv₂ ]
    return $ BaseV bv'
  (PairV ṽ₁ₗ ṽ₁ᵣ, PairV ṽ₂ₗ ṽ₂ᵣ) → sumTup ṽ₁ₗ ṽ₁ᵣ ṽ₂ₗ ṽ₂ᵣ PairV
  (LV ṽ₁, LV ṽ₂) → sumSum True ṽ₁ True ṽ₂
  (LV ṽ₁, RV ṽ₂) → sumSum True ṽ₁ False ṽ₂
  (RV ṽ₁, LV ṽ₂) → sumSum False ṽ₁ True ṽ₂
  (RV ṽ₁, RV ṽ₂) → sumSum False ṽ₁ False ṽ₂
  (NilV, NilV) → return NilV
  (ConsV ṽ₁ₗ ṽ₁ᵣ, ConsV ṽ₂ₗ ṽ₂ᵣ) → sumTup ṽ₁ₗ ṽ₁ᵣ ṽ₂ₗ ṽ₂ᵣ ConsV
  (BulV, BulV) → return BulV
  _ → throwIErrorCxt TypeIError "sumVal: values v₁ and v₂ have different shapes." $ frhs
      [ ("v₁", pretty v₁)
      , ("v₂", pretty v₂)
      ]
  where sumTup ṽ₁ₗ ṽ₁ᵣ ṽ₂ₗ ṽ₂ᵣ constr = do
          us₁ₗ :* us₂ₗ ← (mapM unShareValP $ frhs [ ṽ₁ₗ, ṽ₂ₗ ]) ≫= fromSome ∘ (view two𝐿L)
          usₗ ← sumUnShare us₁ₗ us₂ₗ
          ṽₗ ← reShareValP usₗ
          us₁ᵣ :* us₂ᵣ ← (mapM unShareValP $ frhs [ ṽ₁ᵣ, ṽ₂ᵣ ]) ≫= fromSome ∘ (view two𝐿L)
          usᵣ ← sumUnShare us₁ᵣ us₂ᵣ
          ṽᵣ ← reShareValP usᵣ
          return $ constr ṽₗ ṽᵣ
        sumSum tag₁ ṽ₁ tag₂ ṽ₂ = do
          tag ← (interpPrim PlusO $ frhs [ BoolBV tag₁, BoolBV tag₂ ]) ≫= fromSome ∘ (view boolBVL)
          us₁ :* us₂ ← (mapM unShareValP $ frhs [ ṽ₁, ṽ₂ ]) ≫= fromSome ∘ (view two𝐿L)
          us ← sumUnShare us₁ us₂
          ṽ ← reShareValP us
          return $ if tag then LV ṽ else RV ṽ

sumMPCVal ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ P p → 𝑃 PrinVal → MPCVal p → MPCVal p → IM (MPCVal p)
sumMPCVal p ρvs v̂₁ v̂₂ = case (v̂₁, v̂₂) of
  (DefaultMV, _) → return v̂₂
  (_, DefaultMV) → return v̂₁
  (BulMV, BulMV) → return BulMV
  (BaseMV pv₁, BaseMV pv₂) → do
    pv' ← exePrim p ρvs PlusO $ frhs [ pv₁, pv₂ ]
    return $ BaseMV pv'
  (PairMV v̂₁ₗ v̂₁ᵣ, PairMV v̂₂ₗ v̂₂ᵣ) → sumTup v̂₁ₗ v̂₁ᵣ v̂₂ₗ v̂₂ᵣ
  (SumMV pv₁ v̂₁ₗ v̂₁ᵣ, SumMV pv₂ v̂₂ₗ v̂₂ᵣ) → sumSum pv₁ v̂₁ₗ v̂₁ᵣ pv₂ v̂₂ₗ v̂₂ᵣ
  _ → throwIErrorCxt TypeIError "sumMPCVal: MPC values v̂₁ and v̂₂ have different shapes." $ frhs
      [ ("v̂₁", pretty v̂₁)
      , ("v̂₂", pretty v̂₂)
      ]
  where sumTup v̂₁ₗ v̂₁ᵣ v̂₂ₗ v̂₂ᵣ = do
          v̂ₗ ← sumMPCVal p ρvs v̂₁ₗ v̂₂ₗ
          v̂ᵣ ← sumMPCVal p ρvs v̂₁ᵣ v̂₂ᵣ
          return $ PairMV v̂ₗ v̂ᵣ
        sumSum pv₁ v̂₁ₗ v̂₁ᵣ pv₂ v̂₂ₗ v̂₂ᵣ = do
          tag ← exePrim p ρvs PlusO $ frhs [ pv₁, pv₂ ]
          v̂ₗ ← sumMPCVal p ρvs v̂₁ₗ v̂₂ₗ
          v̂ᵣ ← sumMPCVal p ρvs v̂₁ᵣ v̂₂ᵣ
          return $ SumMV tag v̂ₗ v̂ᵣ

viewPairUnShare ∷ UnShare → FailT IM (UnShare ∧ UnShare)
viewPairUnShare = \case
  NotShared (PairV ṽ₁ ṽ₂) → do
    us₁ ← lift $ unShareValP ṽ₁
    us₂ ← lift $ unShareValP ṽ₂
    return $ us₁ :* us₂
  Shared p sp ρvs (PairMV v̂₁ v̂₂) → return $ Shared p sp ρvs v̂₁ :* Shared p sp ρvs v̂₂
  _ → abort

viewSumUnShare ∷ UnShare → FailT IM (UnShare ∧ UnShare ∧ UnShare)
viewSumUnShare = \case
  NotShared (LV ṽ) → do
    us ← lift $ unShareValP ṽ
    return $ (NotShared $ BaseV $ BoolBV True) :* us :* (NotShared DefaultV)
  NotShared (RV ṽ) → do
    us ← lift $ unShareValP ṽ
    return $ (NotShared $ BaseV $ BoolBV False) :* (NotShared DefaultV) :* us
  Shared p sp ρvs (SumMV pv v̂ₗ v̂ᵣ) → return $ Shared p sp ρvs (BaseMV pv) :* Shared p sp ρvs v̂ₗ :* Shared p sp ρvs v̂ᵣ
  _ → abort

viewNilUnShare ∷ UnShare → FailT IM ()
viewNilUnShare = \case
  NotShared NilV → return ()
  _ → abort

viewConsUnShare ∷ UnShare → FailT IM (UnShare ∧ UnShare)
viewConsUnShare = \case
  NotShared (ConsV ṽ₁ ṽ₂) → do
    us₁ ← lift $ unShareValP ṽ₁
    us₂ ← lift $ unShareValP ṽ₂
    return $ us₁ :* us₂
  _ → abort

-----------------------------------
--- Intro and Elim on Locations ---
-----------------------------------


-}
