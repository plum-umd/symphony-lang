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

withValP ∷ (STACK) ⇒ (Val → IM a) → (Prot → 𝑃 PrinVal → MPCVal → IM a) → ValP → IM a
withValP kVal kMPCVal ṽ = do
  pptraceM "here"
  gm ← askL iCxtGlobalModeL
  case ṽ of
    SSecVP m v → do
      -- (1) All parties executing this code must have the value (gm ⊑ m)
      guardErr (gm ⊑ m) $
        throwIErrorCxt TypeIError "withValP: SSecVP: gm ⋢ m " $ frhs
        [ ("gm",pretty gm)
        , ("m",pretty m)
        ]
      kVal v
    ShareVP φ ρvs v̂ → do
      -- (1) All parties executing this code must have the value (gm ⊑ SecM ρvs) AND
      -- (2) All parties that have the value (i.e. the parties amongst whom the value is shared) must be executing this code (SecM ρvs ⊑ gm)
      guardErr (gm ≡ SecM ρvs) $
        throwIErrorCxt TypeIError "withValP: gm ≢ SecM ρvs" $ frhs
        [ ("gm", pretty gm)
        , ("ρvs", pretty ρvs)
        ]
      kMPCVal φ ρvs v̂
    _ → throwIErrorCxt TypeIError "withValP: ṽ ∉ {SSecVP _ _,ShareVP _ _ _}" $ frhs
        [ ("ṽ",pretty ṽ) ]

-- restrict the mode on a value to be no larger than execution mode
-- e.g.:
-- ‣ if current mode is {par:A,B} and value is {ssec:C} this fails
-- ‣ if current mode is {par:A,B} and value is {ssec:A}, this succeeds
-- ‣ if current mode is {par:A,B} and value is {ssec:A,B}, this succeeds
-- ‣ if current mode is {par:A,B} and value is {ssec:A,B,C}, this succeeds with value in {ssec:A,B}
restrictValP ∷ (STACK) ⇒ ValP → IM ValP
restrictValP ṽ = do
  gm ← askL iCxtGlobalModeL
  case (gm,ṽ) of
    (SecM _ρs₁, SSecVP m v) → do
      v' ← recVal v
      let m' = gm ⊓ m
      return $ SSecVP m' v'
    (SecM ρs, ISecVP ρvs) → do
      ρvs' ← mapM recVal (restrict ρs ρvs)
      return $ ISecVP ρvs'
    (SecM ρs₁, ShareVP φ ρs₂ v) → do
      guardErr (ρs₂ ≡ ρs₁) (throwIErrorCxt TypeIError "restrictValP: ρs₂ ≢ ρs₁" $ frhs
                            [ ("ρs₁",pretty ρs₁)
                            , ("ρs₂",pretty ρs₂)
                            ])
      return $ ShareVP φ ρs₂ v
    (TopM,_) → return ṽ
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
            ArrayV ṽs → ArrayV ∘ vec ^$ mapMOn (list ṽs) restrictValP
            PairV ṽ₁ ṽ₂ → do
              ṽ₁' ← restrictValP ṽ₁
              ṽ₂' ← restrictValP ṽ₂
              return $ PairV ṽ₁' ṽ₂'
            UnknownV _ → return v
            DefaultV → return DefaultV

------------------------------------
--- Intro and Elim on Non-Shares ---
------------------------------------

introValP ∷ (STACK) ⇒ Val → IM ValP
introValP v = do
  gm ← askL iCxtGlobalModeL
  return $ SSecVP gm v

elimValP ∷ (STACK) ⇒ ValP → IM Val
elimValP = withValP return shareError
  where shareError φ ρvs v̂ = throwIErrorCxt TypeIError "elimValP: ShareVP φ ρvs v̂" $ frhs
                                [ ("φ", pretty φ)
                                , ("ρvs", pretty ρvs)
                                , ("v̂", pretty v̂)
                                ]

------------------------------
--- Share / Embed / Reveal ---
------------------------------

shareValP ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ P p → SProt p → PrinVal → ValP → IM MPCVal
shareValP p sp ρvSharer = withValP kShareVal kShareMPCVal
  where kShareVal                    = shareVal p sp ρvSharer (shareValP p sp ρvSharer)
        kShareMPCVal φ ρvsShareees v̂ = throwIErrorCxt NotImplementedIError "shareValP: sharing (ShareVP φ ρvsShareees v̂) unimplemented" $ frhs
                                       [ ("φ", pretty φ)
                                       , ("ρvsShareees", pretty ρvsShareees)
                                       , ("v̂", pretty v̂)
                                       ]

shareVal ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ P p → SProt p → PrinVal → (ValP → IM MPCVal) → Val → IM MPCVal
shareVal p sp ρvSharer kValP = undefined
--  mpcValFrVal p sp kShareBaseV kShareUnknownV kValP
  where kShareBaseV    = mpcValFrBaseVal p sp (Some ρvSharer)
        kShareUnknownV = shareUnknown p sp ρvSharer

shareUnknown ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ P p → SProt p → PrinVal → Type → IM MPCVal
shareUnknown p sp ρvSharer = \case
  BaseT bτ → do
    pv ← exeUnk p ρvSharer bτ
    return $ BaseMV $ Share sp pv
  τ₁ :×: τ₂ → do
    v̂₁ ← shareUnknownR τ₁
    v̂₂ ← shareUnknownR τ₂
    return $ PairMV v̂₁ v̂₂
  τ₁ :+: τ₂ → do
    tag ← exeUnk p ρvSharer 𝔹T ≫= return ∘ Share sp
    v̂₁ ← shareUnknownR τ₁
    v̂₂ ← shareUnknownR τ₂
    return $ SumMV tag v̂₁ v̂₂
  UnitT → return BulMV
  τ → throwIErrorCxt TypeIError "shareUnknown: type τ cannot be shared" $ frhs
      [ ("τ", pretty τ)
      ]
  where shareUnknownR = shareUnknown p sp ρvSharer

embedValP ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → ValP → IM MPCVal
embedValP p sp ρvsShareees = withValP kEmbedVal kEmbedMPCVal
  where kEmbedVal                     = embedVal p sp (embedValP p sp ρvsShareees)
        kEmbedMPCVal φ ρvsShareees' v̂ = do
          sameProt φ sp
          if ρvsShareees ≡ ρvsShareees' then
            return v̂
          else
            throwIErrorCxt TypeIError "embedValP: ρvsShareees ≢ ρvsShareees'" $ frhs
            [ ("ρvsShareees", pretty ρvsShareees)
            , ("ρvsShareees'", pretty ρvsShareees')
            ]

embedVal ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ P p → SProt p → (ValP → IM MPCVal) → Val → IM MPCVal
embedVal p sp kValP = mpcValFrVal p sp kEmbedBaseV kEmbedUnknownV kValP
  where kEmbedBaseV      = mpcValFrBaseVal p sp None
        kEmbedUnknownV τ = throwIErrorCxt TypeIError "embedValP: UnknownV τ cannot be embedded" $ frhs
                           [ ("τ", pretty τ)
                           ]

mpcValFrVal ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ P p → SProt p → (BaseVal → IM MPCVal) → (Type → IM MPCVal) → (ValP → IM MPCVal) → Val → IM MPCVal
mpcValFrVal p sp kBaseV kUnknownV kValP = \case
{-  BaseV bv → kBaseV bv
  PairV ṽ₁ ṽ₂ → do
    v̂₁ ← kValP ṽ₁
    v̂₂ ← kValP ṽ₂
    return $ PairMV v̂₁ v̂₂
  LV ṽ → do
    v̂ ← kValP ṽ
    tt ← exeBaseVal p None (BoolBV True) ≫= return ∘ Share sp
    return $ SumMV tt v̂ DefaultMV
  RV ṽ → do
    v̂ ← kValP ṽ
    ff ← exeBaseVal p None (BoolBV False) ≫= return ∘ Share sp
    return $ SumMV ff DefaultMV v̂
  NilV → return NilMV
  ConsV ṽ₁ ṽ₂ → do
    v̂₁ ← kValP ṽ₁
    v̂₂ ← kValP ṽ₂
    return $ ConsMV v̂₁ v̂₂
  UnknownV τ → kUnknownV τ -}
  v → throwIErrorCxt TypeIError "mpcValFrVal: value v cannot be converted to a MPC value" $ frhs
      [ ("v", pretty v) ]

mpcValFrBaseVal ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ P p → SProt p → 𝑂 PrinVal → BaseVal → IM MPCVal
mpcValFrBaseVal p sp ρvSharer bv = do
  pptraceM "yes..."
  pv ← exeBaseVal p ρvSharer bv
  return $ BaseMV $ Share sp pv

revealValP ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → 𝑃 PrinVal → ValP → IM Val
revealValP p sp ρvsRevealers ρvsRevealees = withValP kRevealVal kRevealMPCVal
  where kRevealVal v                 = throwIErrorCxt NotImplementedIError "revealValP: revealing value v unimplemented" $ frhs
                                       [ ("v", pretty v)
                                       ]
        kRevealMPCVal φ ρvsSharees v̂ = do
          sameProt φ sp
          if ρvsSharees ≡ ρvsRevealers then
            revealMPCVal p sp ρvsRevealees v̂
          else
            throwIErrorCxt TypeIError "revealValP: ρvsRevealers ≢ ρvsSharees" $ frhs
            [ ("ρvsRevealers", pretty ρvsRevealers)
            , ("ρvsSharees", pretty ρvsSharees)
            ]

revealMPCVal ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → MPCVal → IM Val
revealMPCVal p sp ρvsRevealees = \case
  DefaultMV → throwIErrorCxt TypeIError "revealMPCVal: DefaultMV" empty𝐿
  BaseMV sh → do
    pv ← unwrapShare sp sh
    bv ← reveal p ρvsRevealees pv
    return $ BaseV bv
  PairMV v̂₁ v̂₂ → do
    v₁ ← revealMPCValR v̂₁
    v₂ ← revealMPCValR v̂₂
    return $ PairV (toValP v₁) (toValP v₂)
  SumMV sh₁ v̂₂ v̂₃ → do
    pv ← unwrapShare sp sh₁
    bv₁ ← reveal p ρvsRevealees pv
    b₁ ← error𝑂 (view boolBVL bv₁) (throwIErrorCxt TypeIError "revealMPCVal: (view boolBVL bv₁) ≡ None" $ frhs
                                   [ ("bv₁", pretty bv₁)
                                   ])
    let inj :* mv = if b₁ then LV :* (revealMPCValR v̂₂) else RV :* (revealMPCValR v̂₃)
    map (inj ∘ toValP) mv
  NilMV → return NilV
  ConsMV v̂₁ v̂₂ → do
    v₁ ← revealMPCValR v̂₁
    v₂ ← revealMPCValR v̂₂
    return $ ConsV (toValP v₁) (toValP v₂)
  BulMV → return BulV
  where revealMPCValR = revealMPCVal p sp ρvsRevealees
        toValP = SSecVP (SecM ρvsRevealees)

----------------
--- UnShares ---
----------------

unShareValP ∷ (STACK) ⇒ ValP → IM UnShare
unShareValP = withValP (return ∘ NotShared) (\ φ ρvs v̂ → return $ Shared φ ρvs v̂)

reShareValP ∷ (STACK) ⇒ UnShare → IM ValP
reShareValP = \case
  NotShared v    → introValP v
  Shared φ ρvs v̂ → return $ ShareVP φ ρvs v̂

type ShareInfo = 𝑂 (Prot ∧ 𝑃 PrinVal)

shareInfoFrUnShares ∷ (STACK) ⇒ 𝐿 UnShare → IM ShareInfo
shareInfoFrUnShares uvs = joinShareInfos sis
  where sis = mapOn uvs shareInfoFrUnShare

joinShareInfos ∷ (STACK) ⇒ 𝐿 ShareInfo → IM ShareInfo
joinShareInfos = mfoldFromWith None joinShareInfo

shareInfoFrUnShare ∷ UnShare → ShareInfo
shareInfoFrUnShare = \case
  NotShared _v    → None
  Shared φ ρvs _v̂ → Some $ φ :* ρvs

joinShareInfo ∷ (STACK) ⇒ ShareInfo → ShareInfo → IM ShareInfo
joinShareInfo si₁ si₂ = case (si₁, si₂) of
  (None, _   ) → return si₂
  (_   , None) → return si₁
  (Some (φ₁ :* ρvs₁), Some (φ₂ :* ρvs₂)) →
    if (φ₁ ≡ φ₂) ⩓ (ρvs₁ ≡ ρvs₂) then
      return $ Some $ φ₁ :* ρvs₁
    else
      throwIErrorCxt TypeIError "joinShareInfo: φ₁ ≡ φ₂ ⩓ ρvs₁ ≡ ρvs₂ does not hold" $ frhs
      [ ("φ₁", pretty φ₁)
      , ("φ₂", pretty φ₂)
      , ("ρvs₁", pretty ρvs₁)
      , ("ρvs₂", pretty ρvs₂)
      ]

unwrapUnShares ∷ (STACK) ⇒ 𝐿 UnShare → IM (𝐿 Val ∨ (Prot ∧ 𝑃 PrinVal ∧ 𝐿 MPCVal))
unwrapUnShares uvs = do
  si ← shareInfoFrUnShares uvs
  case si of
    None →
      return $ Inl vs
      where vs = mapOn uvs $ \ (NotShared v) → v
    Some (φ :* ρvs) → do
      v̂s ← mapMOn uvs $ \ uv →
        case uv of
          NotShared v → withProt φ $ \ p sp → embedVal p sp (embedValP p sp ρvs)  v
          Shared _φ _ρvs v̂ → return v̂
      return $ Inr $ φ :* ρvs :* v̂s

primUnShare ∷ (STACK) ⇒ Op → 𝐿 UnShare → IM UnShare
primUnShare op uss = do
  vsorv̂s ← unwrapUnShares uss
  case vsorv̂s of
    Inl vs → do
      bvs ← error𝑂 (mapMOn vs $ view baseVL) (throwIErrorCxt TypeIError "primUnShare: mapMOn vs $ view baseVL ≡ None" $ frhs
                                              [ ("vs", pretty vs)
                                              ])
      bv' ← interpPrim op bvs
      return $ NotShared $ BaseV bv'
    Inr (φ :* ρvs :* v̂s) → do
      shs ← error𝑂 (mapMOn v̂s $ view baseMVL) (throwIErrorCxt TypeIError "primUnShare: mapMOn v̂s $ view baseMVL ≡ None" $ frhs
                                              [ ("v̂s", pretty v̂s)
                                              ])
      sh' ← withProt φ $ \ p sp → do
        pvs ← mapMOn shs $ \ sh → unwrapShare sp sh
        pv' ← exePrim p op pvs
        return $ Share sp pv'
      return $ Shared φ ρvs $ BaseMV sh'

notUnShare ∷ (STACK) ⇒ UnShare → IM UnShare
notUnShare us = primUnShare NotO $ frhs [ us ]

muxUnShare ∷ (STACK) ⇒ UnShare → UnShare → UnShare → IM UnShare
muxUnShare us₁ us₂ us₃ = do
  vsorv̂s ← unwrapUnShares $ frhs [ us₁, us₂, us₃ ]
  case vsorv̂s of
    Inl (v₁ :& v₂ :& v₃ :& Nil) → do
      bv₁ ← error𝑂 (view baseVL v₁) (throwIErrorCxt TypeIError "muxUnShare: view baseVL v₁ ≡ None" $ frhs
                                    [ ("v₁", pretty v₁)
                                    ])
      v' ← muxVal bv₁ v₂ v₃
      return $ NotShared v'
    Inr (φ :* ρvs :* (v̂₁ :& v̂₂ :& v̂₃ :& Nil)) → do
      sh₁ ← error𝑂 (view baseMVL v̂₁) (throwIErrorCxt TypeIError "muxUnShare: view baseMVL v̂₁ ≡ None" $ frhs
                                      [ ("v̂₁", pretty v̂₁)
                                      ])
      v̂' ← withProt φ $ \ p sp → muxMPCVal p sp sh₁ v̂₂ v̂₃
      return $ Shared φ ρvs v̂'
    _ → impossible

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
  (LV ṽ₂, LV ṽ₃) → muxSum True ṽ₂ True ṽ₃
  (DefaultV, RV ṽ₃) → do
    ṽ₂ ← introValP DefaultV
    muxSum False ṽ₂ False ṽ₃
  (RV ṽ₂, DefaultV) → do
    ṽ₃ ← introValP DefaultV
    muxSum False ṽ₂ False ṽ₃
  (RV ṽ₂, RV ṽ₃) → muxSum False ṽ₂ False ṽ₃
  (LV ṽ₂, RV ṽ₃) → muxSum False ṽ₂ True ṽ₃
  (RV ṽ₂, LV ṽ₃) → muxSum True ṽ₂ False ṽ₃
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
          return $ if tag then RV ṽ' else LV ṽ'

muxMPCVal ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ P p → SProt p → Share → MPCVal → MPCVal → IM MPCVal
muxMPCVal p sp sh₁ v̂₂ v̂₃ = case (v̂₂, v̂₃) of
  (DefaultMV, DefaultMV) → return DefaultMV
  (DefaultMV, BaseMV sh₃) → do
    pv₁ ← unwrapShare sp sh₁
    pv₃ ← unwrapShare sp sh₃
    pv₂ ← exeBaseVal p None (defaultBaseValOf $ typeOf p pv₃)
    pv' ← exePrim p CondO $ frhs [ pv₁, pv₂, pv₃ ]
    return $ BaseMV $ Share sp pv'
  (BaseMV sh₂, DefaultMV) → do
    pv₁ ← unwrapShare sp sh₁
    pv₂ ← unwrapShare sp sh₂
    pv₃ ← exeBaseVal p None (defaultBaseValOf $ typeOf p pv₂)
    pv' ← exePrim p CondO $ frhs [ pv₁, pv₂, pv₃ ]
    return $ BaseMV $ Share sp pv'
  (BaseMV sh₂, BaseMV sh₃) → do
    pv₁ ← unwrapShare sp sh₁
    pv₂ ← unwrapShare sp sh₂
    pv₃ ← unwrapShare sp sh₃
    pv' ← exePrim p CondO $ frhs [ pv₁, pv₂, pv₃ ]
    return $ BaseMV $ Share sp pv'
  (DefaultMV, PairMV v̂₃ₗ v̂₃ᵣ) → muxTup DefaultMV DefaultMV v̂₃ₗ v̂₃ᵣ PairMV
  (PairMV v̂₂ₗ v̂₂ᵣ, DefaultMV) → muxTup v̂₂ₗ v̂₂ᵣ DefaultMV DefaultMV PairMV
  (PairMV v̂₂ₗ v̂₂ᵣ, PairMV v̂₃ₗ v̂₃ᵣ) → muxTup v̂₂ₗ v̂₂ᵣ v̂₃ₗ v̂₃ᵣ PairMV
  (DefaultMV, SumMV sh₃ v̂₃ₗ v̂₃ᵣ) → do
    pv₂ ← exeBaseVal p None (BoolBV False)
    muxSum (Share sp pv₂) DefaultMV DefaultMV sh₃ v̂₃ₗ v̂₃ᵣ
  (SumMV sh₂ v̂₂ₗ v̂₂ᵣ, DefaultMV) → do
    pv₃ ← exeBaseVal p None (BoolBV False)
    muxSum sh₂ v̂₂ₗ v̂₂ᵣ (Share sp pv₃) DefaultMV DefaultMV
  (SumMV sh₂ v̂₂ₗ v̂₂ᵣ, SumMV sh₃ v̂₃ₗ v̂₃ᵣ) → muxSum sh₂ v̂₂ₗ v̂₂ᵣ sh₃ v̂₃ₗ v̂₃ᵣ
  (DefaultMV, NilMV) → return NilMV
  (NilMV, DefaultMV) → return NilMV
  (NilMV, NilMV) → return NilMV
  (DefaultMV, ConsMV v̂₃ₗ v̂₃ᵣ) → muxTup DefaultMV DefaultMV v̂₃ₗ v̂₃ᵣ ConsMV
  (ConsMV v̂₂ₗ v̂₂ᵣ, DefaultMV) → muxTup v̂₂ₗ v̂₂ᵣ DefaultMV DefaultMV ConsMV
  (ConsMV v̂₂ₗ v̂₂ᵣ, ConsMV v̂₃ₗ v̂₃ᵣ) → muxTup v̂₂ₗ v̂₂ᵣ v̂₃ₗ v̂₃ᵣ ConsMV
  _ → throwIErrorCxt TypeIError "muxMPCVal: MPC values v̂₂ and v̂₃ have different shapes." $ frhs
      [ ("v̂₂", pretty v̂₂)
      , ("v̂₃", pretty v̂₃)
      ]
  where muxTup v̂₂ₗ v̂₂ᵣ v̂₃ₗ v̂₃ᵣ constr = do
          v̂ₗ ← muxMPCVal p sp sh₁ v̂₂ₗ v̂₃ₗ
          v̂ᵣ ← muxMPCVal p sp sh₁ v̂₂ᵣ v̂₃ᵣ
          return $ constr v̂ₗ v̂ᵣ
        muxSum sh₂ v̂₂ₗ v̂₂ᵣ sh₃ v̂₃ₗ v̂₃ᵣ = do
          tag₁ ← unwrapShare sp sh₁
          tag₂ ← unwrapShare sp sh₂
          tag₃ ← unwrapShare sp sh₃
          tag ← exePrim p CondO $ frhs [ tag₁, tag₂, tag₃ ]
          v̂ₗ ← muxMPCVal p sp sh₁ v̂₂ₗ v̂₃ₗ
          v̂ᵣ ← muxMPCVal p sp sh₁ v̂₂ᵣ v̂₃ᵣ
          return $ SumMV (Share sp tag) v̂ₗ v̂ᵣ

defaultBaseValOf ∷ BaseType → BaseVal
defaultBaseValOf = \case
  𝔹T → BoolBV False
  ℕT pr → NatBV pr 0
  ℤT pr → IntBV pr $ HS.fromIntegral 0
  𝔽T pr → FltBV pr $ HS.fromIntegral 0

sumUnShare ∷ (STACK) ⇒ UnShare → UnShare → IM UnShare
sumUnShare us₁ us₂ = do
  vsorv̂s ← unwrapUnShares $ frhs [ us₁, us₂ ]
  case vsorv̂s of
    Inl vs → do
      v₁ :* v₂ ← fromSome $ view two𝐿L vs
      v' ← sumVal v₁ v₂
      return $ NotShared v'
    Inr (φ :* ρvs :* v̂s) → do
      v̂₁ :* v̂₂ ← fromSome $ view two𝐿L v̂s
      v̂' ← withProt φ $ \ p sp → sumMPCVal p sp v̂₁ v̂₂
      return $ Shared φ ρvs v̂'

sumVal ∷ (STACK) ⇒ Val → Val → IM Val
sumVal v₁ v₂ = case (v₁, v₂) of
  (_, DefaultV) → return v₁
  (DefaultV, _) → return v₂
  (BaseV bv₁, BaseV bv₂) → do
    bv' ← interpPrim PlusO $ frhs [ bv₁, bv₂ ]
    return $ BaseV bv'

sumMPCVal ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ P p → SProt p → MPCVal → MPCVal → IM MPCVal
sumMPCVal = undefined

viewPairUnShare ∷ UnShare → FailT IM (UnShare ∧ UnShare)
viewPairUnShare = \case
  NotShared (PairV ṽ₁ ṽ₂) → do
    us₁ ← lift $ unShareValP ṽ₁
    us₂ ← lift $ unShareValP ṽ₂
    return $ us₁ :* us₂
  Shared φ ρvs (PairMV v̂₁ v̂₂) → return $ Shared φ ρvs v̂₁ :* Shared φ ρvs v̂₂
  _ → abort

-----------------------------------
--- Intro and Elim on Locations ---
-----------------------------------

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
