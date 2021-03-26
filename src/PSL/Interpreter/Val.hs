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

withValP ∷ (Monad m,MonadReader ICxt m,MonadError IError m,STACK) ⇒ (Val → ReaderT r m a) → (Prot → 𝑃 PrinVal → MPCVal → ReaderT r m a) → ValP → ReaderT r m a
withValP kVal kMPCVal ṽ = do
  gm ← lift $ askL iCxtGlobalModeL
  case ṽ of
    SSecVP m v → do
      -- (1) All parties executing this code must have the value (gm ⊑ m)
      guardErr (gm ⊑ m) $
        lift $ throwIErrorCxt TypeIError "withValP: SSecVP: gm ⋢ m " $ frhs
               [ ("gm",pretty gm)
               , ("m",pretty m)
               ]
      kVal v
    ShareVP φ ρvs v̂ → do
      -- (1) All parties executing this code must have the value (gm ⊑ SecM ρvs) AND
      -- (2) All parties that have the value (i.e. the parties amongst whom the value is shared) must be executing this code (SecM ρvs ⊑ gm)
      guardErr (gm ≡ SecM ρvs) $
        lift $ throwIErrorCxt TypeIError "withValP: gm ≢ SecM ρvs" $ frhs
               [ ("gm", pretty gm)
               , ("ρvs", pretty ρvs)
               ]
      kMPCVal φ ρvs v̂
    _ → lift $ throwIErrorCxt TypeIError "withValP: ṽ ∉ {SSecVP _ _,ShareVP _ _ _}" $ frhs
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
            ArrayV ṽs → ArrayV ∘ spvec𝐼 ^$ mapMOn (iter ṽs) (mapMSnd restrictValP)
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
elimValP = runReaderT () ∘ (withValP return shareError)
  where shareError φ ρvs v̂ = throwIErrorCxt TypeIError "elimValP: ShareVP φ ρvs v̂" $ frhs
                                [ ("φ", pretty φ)
                                , ("ρvs", pretty ρvs)
                                , ("v̂", pretty v̂)
                                ]

------------------------------
--- Share / Embed / Reveal ---
------------------------------

data Sharing p = Sharing (P p) (SProt p) PrinVal (𝑃 PrinVal)

sharingProxyL ∷ ∀ (p ∷ Prot). (Protocol p) ⇒ Sharing p ⟢ P p
sharingProxyL = lens getProxy setProxy
  where getProxy (Sharing p _ _ _) = p
        setProxy (Sharing _ sp ρv ρvs) p = Sharing p sp ρv ρvs

sharingSProtL ∷ ∀ (p ∷ Prot). (Protocol p) ⇒ Sharing p ⟢ SProt p
sharingSProtL = lens getSProt setSProt
  where getSProt (Sharing _ sp _ _) = sp
        setSProt (Sharing p _ ρv ρvs) sp = Sharing p sp ρv ρvs

sharingSharerL ∷ ∀ (p ∷ Prot). (Protocol p) ⇒ Sharing p ⟢ PrinVal
sharingSharerL = lens getSharer setSharer
  where getSharer (Sharing _ _ ρv _) = ρv
        setSharer (Sharing p sp _ ρvs) ρv = Sharing p sp ρv ρvs

sharingShareeesL ∷ ∀ (p ∷ Prot). (Protocol p) ⇒ Sharing p ⟢ 𝑃 PrinVal
sharingShareeesL = lens getShareees setShareees
  where getShareees (Sharing _ _ _ ρvs) = ρvs
        setShareees (Sharing p sp ρv _) ρvs = Sharing p sp ρv ρvs

shareValP ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ ValP → ReaderT (Sharing p) IM ValP
shareValP ṽ = do
  φ   ← map protFrSProt $ askL sharingSProtL
  ρvs ← askL sharingShareeesL
  v̂   ← shareValPToMPC ṽ
  lift $ reShareMPCVal φ ρvs v̂

shareValPToMPC ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ ValP → ReaderT (Sharing p) IM MPCVal
shareValPToMPC = withValP shareValToMPC kShareMPCVal
  where kShareMPCVal φ ρvsShareees v̂ = lift $ throwIErrorCxt NotImplementedIError "shareValP: sharing (ShareVP φ ρvsShareees v̂) unimplemented" $ frhs
                                              [ ("φ", pretty φ)
                                              , ("ρvsShareees", pretty ρvsShareees)
                                              , ("v̂", pretty v̂)
                                              ]

shareValToMPC ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ Val → ReaderT (Sharing p) IM MPCVal
shareValToMPC = mpcValFrVal kShareBaseV shareUnknownToMPC shareValPToMPC
  where kShareBaseV bv = do
          p   ← askL sharingProxyL
          sp  ← askL sharingSProtL
          ρv  ← askL sharingSharerL
          ρvs ← askL sharingShareeesL
          pv  ← lift $ shareBaseVal p ρvs ρv bv
          return $ BaseMV $ Share sp pv

shareUnknownToMPC ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ Type → ReaderT (Sharing p) IM MPCVal
shareUnknownToMPC τ = do
  p  ← askL sharingProxyL
  sp ← askL sharingSProtL
  ρv ← askL sharingSharerL
  ρvs ← askL sharingShareeesL
  case τ of
    BaseT bτ → do
      pv ← lift $ shareUnk p ρvs ρv bτ
      return $ BaseMV $ Share sp pv
    τ₁ :×: τ₂ → do
      v̂₁ ← shareUnknownToMPC τ₁
      v̂₂ ← shareUnknownToMPC τ₂
      return $ PairMV v̂₁ v̂₂
    τ₁ :+: τ₂ → do
      tag ← lift $ shareUnk p ρvs ρv 𝔹T ≫= return ∘ Share sp
      v̂₁ ← shareUnknownToMPC τ₁
      v̂₂ ← shareUnknownToMPC τ₂
      return $ SumMV tag v̂₁ v̂₂
    UnitT → return BulMV
    _ → lift $ throwIErrorCxt TypeIError "shareUnknown: type τ cannot be shared" $ frhs
               [ ("τ", pretty τ)
               ]

embedValP ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ ValP → ReaderT (Sharing p) IM ValP
embedValP ṽ = do
  φ   ← map protFrSProt $ askL sharingSProtL
  ρvs ← askL sharingShareeesL
  v̂   ← embedValPToMPC ṽ
  lift $ reShareMPCVal φ ρvs v̂

embedValPToMPC ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ ValP → ReaderT (Sharing p) IM MPCVal
embedValPToMPC = withValP embedValToMPC kEmbedMPCVal
  where kEmbedMPCVal φ ρvs' v̂ = do
          sp ← askL sharingSProtL
          ρvs ← askL sharingShareeesL
          lift $ sameProt φ sp
          if ρvs ≡ ρvs' then
            return v̂
          else
            lift $ throwIErrorCxt TypeIError "embedValP: ρvs ≢ ρvs'" $ frhs
                   [ ("ρvs", pretty ρvs)
                   , ("ρvs'", pretty ρvs')
                   ]

embedValToMPC ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ Val → ReaderT (Sharing p) IM MPCVal
embedValToMPC = mpcValFrVal kEmbedBaseV kEmbedUnknownV embedValPToMPC
  where kEmbedBaseV bv = do
          p  ← askL sharingProxyL
          sp ← askL sharingSProtL
          ρvs ← askL sharingShareeesL
          pv ← lift $ embedBaseVal p ρvs bv
          return $ BaseMV $ Share sp pv
        kEmbedUnknownV τ = lift $ throwIErrorCxt TypeIError "embedValP: UnknownV τ cannot be embedded" $ frhs
                                  [ ("τ", pretty τ)
                                  ]

mpcValFrVal ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ (BaseVal → ReaderT (Sharing p) IM MPCVal) →
                                                  (Type    → ReaderT (Sharing p) IM MPCVal) →
                                                  (ValP    → ReaderT (Sharing p) IM MPCVal) →
                                                  Val                                       →
                                                  ReaderT (Sharing p) IM MPCVal
mpcValFrVal kBaseV kUnknownV kValP v = do
  p ← askL sharingProxyL
  sp ← askL sharingSProtL
  ρvs ← askL sharingShareeesL
  case v of
    DefaultV → return DefaultMV
    BulV → return BulMV
    BaseV bv → kBaseV bv
    PairV ṽ₁ ṽ₂ → do
      v̂₁ ← kValP ṽ₁
      v̂₂ ← kValP ṽ₂
      return $ PairMV v̂₁ v̂₂
    LV ṽ → do
      v̂ ← kValP ṽ
      tt ← lift $ embedBaseVal p ρvs (BoolBV True) ≫= return ∘ Share sp
      return $ SumMV tt v̂ DefaultMV
    RV ṽ → do
      v̂ ← kValP ṽ
      ff ← lift $ embedBaseVal p ρvs (BoolBV False) ≫= return ∘ Share sp
      return $ SumMV ff DefaultMV v̂
    NilV → return NilMV
    ConsV ṽ₁ ṽ₂ → do
      v̂₁ ← kValP ṽ₁
      v̂₂ ← kValP ṽ₂
      return $ ConsMV v̂₁ v̂₂
    UnknownV τ → kUnknownV τ
    _ → lift $ throwIErrorCxt TypeIError "mpcValFrVal: value v cannot be converted to a MPC value" $ frhs
               [ ("v", pretty v) ]

data Revealing p = Revealing (P p) (SProt p) (𝑃 PrinVal) (𝑃 PrinVal)

revealingProxyL ∷ ∀ (p ∷ Prot). (Protocol p) ⇒ Revealing p ⟢ P p
revealingProxyL = lens getProxy setProxy
  where getProxy (Revealing p _ _ _) = p
        setProxy (Revealing _ sp ρvs₁ ρvs₂) p = Revealing p sp ρvs₁ ρvs₂

revealingSProtL ∷ ∀ (p ∷ Prot). (Protocol p) ⇒ Revealing p ⟢ SProt p
revealingSProtL = lens getSProt setSProt
  where getSProt (Revealing _ sp _ _) = sp
        setSProt (Revealing p _ ρvs₁ ρvs₂) sp = Revealing p sp ρvs₁ ρvs₂

revealingRevealersL ∷ ∀ (p ∷ Prot). (Protocol p) ⇒ Revealing p ⟢ 𝑃 PrinVal
revealingRevealersL = lens getRevealers setRevealers
  where getRevealers (Revealing _ _ ρvs₁ _) = ρvs₁
        setRevealers (Revealing p sp _ ρvs₂) ρvs₁ = Revealing p sp ρvs₁ ρvs₂

revealingRevealeesL ∷ ∀ (p ∷ Prot). (Protocol p) ⇒ Revealing p ⟢ 𝑃 PrinVal
revealingRevealeesL = lens getRevealees setRevealees
  where getRevealees (Revealing _ _ _ ρvs₂) = ρvs₂
        setRevealees (Revealing p sp ρvs₁ _) ρvs₂ = Revealing p sp ρvs₁ ρvs₂

revealValP ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ ValP → ReaderT (Revealing p) IM ValP
revealValP ṽ = do
  ρvs ← askL revealingRevealeesL
  v ← withValP revealVal kRevealMPCVal ṽ
  return $ SSecVP (SecM ρvs) v
  where kRevealMPCVal φ ρvs' v̂ = do
          sp  ← askL revealingSProtL
          ρvs ← askL revealingRevealersL
          lift $ sameProt φ sp
          if ρvs ≡ ρvs' then
            revealMPCVal v̂
          else
            lift $ throwIErrorCxt TypeIError "revealValP: ρvs ≢ ρvs'" $ frhs
                   [ ("ρvs", pretty ρvs)
                   , ("ρvs'", pretty ρvs')
                   ]

revealVal ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ Val → ReaderT (Revealing p) IM Val
revealVal v = case v of
  DefaultV → return v
  BulV → return v
  BaseV _bv → return v
  PairV ṽ₁ ṽ₂ → do
    ṽ₁' ← revealValP ṽ₁
    ṽ₂' ← revealValP ṽ₂
    return $ PairV ṽ₁' ṽ₂'
  LV ṽ' → do
    ṽ'' ← revealValP ṽ'
    return $ LV ṽ''
  RV ṽ' → do
    ṽ'' ← revealValP ṽ'
    return $ RV ṽ''
  NilV → return v
  ConsV ṽ₁ ṽ₂ → do
    ṽ₁' ← revealValP ṽ₁
    ṽ₂' ← revealValP ṽ₂
    return $ ConsV ṽ₁' ṽ₂'
  _ → lift $ throwIErrorCxt NotImplementedIError "revealVal: revealing value v unimplemented" $ frhs
             [ ("v", pretty v)
             ]

revealMPCVal ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ MPCVal → ReaderT (Revealing p) IM Val
revealMPCVal v̂ = do
  p   ← askL revealingProxyL
  sp  ← askL revealingSProtL
  ρvsFr ← askL revealingRevealersL
  ρvsTo ← askL revealingRevealeesL
  let toValP = SSecVP (SecM ρvsTo)
  case v̂ of
    DefaultMV → lift $ throwIErrorCxt TypeIError "revealMPCVal: DefaultMV" empty𝐿
    BaseMV sh → lift $ do
      pv ← unwrapShare sp sh
      bv ← reveal p ρvsFr ρvsTo pv
      return $ BaseV bv
    PairMV v̂₁ v̂₂ → do
      v₁ ← revealMPCVal v̂₁
      v₂ ← revealMPCVal v̂₂
      return $ PairV (toValP v₁) (toValP v₂)
    SumMV sh₁ v̂₂ v̂₃ → do
      pv  ← lift $ unwrapShare sp sh₁
      bv₁ ← lift $ reveal p ρvsFr ρvsTo pv
      b₁  ← lift $ error𝑂 (view boolBVL bv₁) (throwIErrorCxt TypeIError "revealMPCVal: (view boolBVL bv₁) ≡ None" $ frhs
                                              [ ("bv₁", pretty bv₁)
                                              ])
      let inj :* mv = if b₁ then LV :* (revealMPCVal v̂₂) else RV :* (revealMPCVal v̂₃)
      map (inj ∘ toValP) mv
    NilMV → return NilV
    ConsMV v̂₁ v̂₂ → do
      v₁ ← revealMPCVal v̂₁
      v₂ ← revealMPCVal v̂₂
      return $ ConsV (toValP v₁) (toValP v₂)
    BulMV → return BulV

----------------
--- UnShares ---
----------------

unShareValP ∷ (STACK) ⇒ ValP → IM UnShare
unShareValP = runReaderT () ∘ (withValP (return ∘ NotShared) (\ φ ρvs v̂ → return $ Shared φ ρvs v̂))

reShareValP ∷ (STACK) ⇒ UnShare → IM ValP
reShareValP = \case
  NotShared v    → introValP v
  Shared φ ρvs v̂ → reShareMPCVal φ ρvs v̂

reShareMPCVal ∷ (STACK) ⇒ Prot → 𝑃 PrinVal → MPCVal → IM ValP
reShareMPCVal φ ρvs = \case
  DefaultMV → return $ SSecVP (SecM ρvs) DefaultV
  BulMV     → return $ SSecVP (SecM ρvs) BulV
  BaseMV sh → return $ ShareVP φ ρvs $ BaseMV sh
  PairMV v̂₁ v̂₂ → do
    ṽ₁ ← reShareMPCVal φ ρvs v̂₁
    ṽ₂ ← reShareMPCVal φ ρvs v̂₂
    return $ SSecVP (SecM ρvs) $ PairV ṽ₁ ṽ₂
  SumMV sh₁ v̂₂ v̂₃ → return $ ShareVP φ ρvs $ SumMV sh₁ v̂₂ v̂₃
  NilMV → return $ SSecVP (SecM ρvs) NilV
  ConsMV v̂₁ v̂₂ → do
    ṽ₁ ← reShareMPCVal φ ρvs v̂₁
    ṽ₂ ← reShareMPCVal φ ρvs v̂₂
    return $ SSecVP (SecM ρvs) $ ConsV ṽ₁ ṽ₂

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
          NotShared v → do
            ρv ← fromSome $ (map fst) $ pmin ρvs
            withProt φ $ \ p sp → runReaderT (Sharing p sp ρv ρvs) $ embedValToMPC v
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
        pv' ← exePrim p ρvs op pvs
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
      v̂' ← withProt φ $ \ p sp → muxMPCVal p sp ρvs sh₁ v̂₂ v̂₃
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

muxMPCVal ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → Share → MPCVal → MPCVal → IM MPCVal
muxMPCVal p sp ρvs sh₁ v̂₂ v̂₃ = case (v̂₂, v̂₃) of
  (DefaultMV, DefaultMV) → return DefaultMV
  (DefaultMV, BaseMV sh₃) → do
    pv₁ ← unwrapShare sp sh₁
    pv₃ ← unwrapShare sp sh₃
    pv₂ ← embedBaseVal p ρvs (defaultBaseValOf $ typeOf p pv₃)
    pv' ← exePrim p ρvs CondO $ frhs [ pv₁, pv₂, pv₃ ]
    return $ BaseMV $ Share sp pv'
  (BaseMV sh₂, DefaultMV) → do
    pv₁ ← unwrapShare sp sh₁
    pv₂ ← unwrapShare sp sh₂
    pv₃ ← embedBaseVal p ρvs (defaultBaseValOf $ typeOf p pv₂)
    pv' ← exePrim p ρvs CondO $ frhs [ pv₁, pv₂, pv₃ ]
    return $ BaseMV $ Share sp pv'
  (BaseMV sh₂, BaseMV sh₃) → do
    pv₁ ← unwrapShare sp sh₁
    pv₂ ← unwrapShare sp sh₂
    pv₃ ← unwrapShare sp sh₃
    pv' ← exePrim p ρvs CondO $ frhs [ pv₁, pv₂, pv₃ ]
    return $ BaseMV $ Share sp pv'
  (DefaultMV, PairMV v̂₃ₗ v̂₃ᵣ) → muxTup DefaultMV DefaultMV v̂₃ₗ v̂₃ᵣ PairMV
  (PairMV v̂₂ₗ v̂₂ᵣ, DefaultMV) → muxTup v̂₂ₗ v̂₂ᵣ DefaultMV DefaultMV PairMV
  (PairMV v̂₂ₗ v̂₂ᵣ, PairMV v̂₃ₗ v̂₃ᵣ) → muxTup v̂₂ₗ v̂₂ᵣ v̂₃ₗ v̂₃ᵣ PairMV
  (DefaultMV, SumMV sh₃ v̂₃ₗ v̂₃ᵣ) → do
    pv₂ ← embedBaseVal p ρvs (BoolBV False)
    muxSum (Share sp pv₂) DefaultMV DefaultMV sh₃ v̂₃ₗ v̂₃ᵣ
  (SumMV sh₂ v̂₂ₗ v̂₂ᵣ, DefaultMV) → do
    pv₃ ← embedBaseVal p ρvs (BoolBV False)
    muxSum sh₂ v̂₂ₗ v̂₂ᵣ (Share sp pv₃) DefaultMV DefaultMV
  (SumMV sh₂ v̂₂ₗ v̂₂ᵣ, SumMV sh₃ v̂₃ₗ v̂₃ᵣ) → muxSum sh₂ v̂₂ₗ v̂₂ᵣ sh₃ v̂₃ₗ v̂₃ᵣ
  (DefaultMV, NilMV) → return NilMV
  (NilMV, DefaultMV) → return NilMV
  (NilMV, NilMV) → return NilMV
  (DefaultMV, ConsMV v̂₃ₗ v̂₃ᵣ) → muxTup DefaultMV DefaultMV v̂₃ₗ v̂₃ᵣ ConsMV
  (ConsMV v̂₂ₗ v̂₂ᵣ, DefaultMV) → muxTup v̂₂ₗ v̂₂ᵣ DefaultMV DefaultMV ConsMV
  (ConsMV v̂₂ₗ v̂₂ᵣ, ConsMV v̂₃ₗ v̂₃ᵣ) → muxTup v̂₂ₗ v̂₂ᵣ v̂₃ₗ v̂₃ᵣ ConsMV
  (DefaultMV, BulMV) → return BulMV
  (BulMV, DefaultMV) → return BulMV
  (BulMV, BulMV) → return BulMV
  _ → throwIErrorCxt TypeIError "muxMPCVal: MPC values v̂₂ and v̂₃ have different shapes." $ frhs
      [ ("v̂₂", pretty v̂₂)
      , ("v̂₃", pretty v̂₃)
      ]
  where muxTup v̂₂ₗ v̂₂ᵣ v̂₃ₗ v̂₃ᵣ constr = do
          v̂ₗ ← muxMPCVal p sp ρvs sh₁ v̂₂ₗ v̂₃ₗ
          v̂ᵣ ← muxMPCVal p sp ρvs sh₁ v̂₂ᵣ v̂₃ᵣ
          return $ constr v̂ₗ v̂ᵣ
        muxSum sh₂ v̂₂ₗ v̂₂ᵣ sh₃ v̂₃ₗ v̂₃ᵣ = do
          tag₁ ← unwrapShare sp sh₁
          tag₂ ← unwrapShare sp sh₂
          tag₃ ← unwrapShare sp sh₃
          tag ← exePrim p ρvs CondO $ frhs [ tag₁, tag₂, tag₃ ]
          v̂ₗ ← muxMPCVal p sp ρvs sh₁ v̂₂ₗ v̂₃ₗ
          v̂ᵣ ← muxMPCVal p sp ρvs sh₁ v̂₂ᵣ v̂₃ᵣ
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
      v̂' ← withProt φ $ \ p sp → sumMPCVal p sp ρvs v̂₁ v̂₂
      return $ Shared φ ρvs v̂'

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

sumMPCVal ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → MPCVal → MPCVal → IM MPCVal
sumMPCVal p sp ρvs v̂₁ v̂₂ = case (v̂₁, v̂₂) of
  (DefaultMV, _) → return v̂₂
  (_, DefaultMV) → return v̂₁
  (BaseMV sh₁, BaseMV sh₂) → do
    pv₁ ← unwrapShare sp sh₁
    pv₂ ← unwrapShare sp sh₂
    pv' ← exePrim p ρvs PlusO $ frhs [ pv₁, pv₂ ]
    return $ BaseMV $ Share sp pv'
  (PairMV v̂₁ₗ v̂₁ᵣ, PairMV v̂₂ₗ v̂₂ᵣ) → sumTup v̂₁ₗ v̂₁ᵣ v̂₂ₗ v̂₂ᵣ PairMV
  (SumMV sh₁ v̂₁ₗ v̂₁ᵣ, SumMV sh₂ v̂₂ₗ v̂₂ᵣ) → sumSum sh₁ v̂₁ₗ v̂₁ᵣ sh₂ v̂₂ₗ v̂₂ᵣ
  (NilMV, NilMV) → return NilMV
  (ConsMV v̂₁ₗ v̂₁ᵣ, ConsMV v̂₂ₗ v̂₂ᵣ) → sumTup v̂₁ₗ v̂₁ᵣ v̂₂ₗ v̂₂ᵣ ConsMV
  (BulMV, BulMV) → return BulMV
  _ → throwIErrorCxt TypeIError "sumMPCVal: MPC values v̂₁ and v̂₂ have different shapes." $ frhs
      [ ("v̂₁", pretty v̂₁)
      , ("v̂₂", pretty v̂₂)
      ]
  where sumTup v̂₁ₗ v̂₁ᵣ v̂₂ₗ v̂₂ᵣ constr = do
          v̂ₗ ← sumMPCVal p sp ρvs v̂₁ₗ v̂₂ₗ
          v̂ᵣ ← sumMPCVal p sp ρvs v̂₁ᵣ v̂₂ᵣ
          return $ constr v̂ₗ v̂ᵣ
        sumSum sh₁ v̂₁ₗ v̂₁ᵣ sh₂ v̂₂ₗ v̂₂ᵣ = do
          tag₁ ← unwrapShare sp sh₁
          tag₂ ← unwrapShare sp sh₂
          tag ← exePrim p ρvs PlusO $ frhs [ tag₁, tag₂ ]
          v̂ₗ ← sumMPCVal p sp ρvs v̂₁ₗ v̂₂ₗ
          v̂ᵣ ← sumMPCVal p sp ρvs v̂₁ᵣ v̂₂ᵣ
          return $ SumMV (Share sp tag) v̂ₗ v̂ᵣ

viewPairUnShare ∷ UnShare → FailT IM (UnShare ∧ UnShare)
viewPairUnShare = \case
  NotShared (PairV ṽ₁ ṽ₂) → do
    us₁ ← lift $ unShareValP ṽ₁
    us₂ ← lift $ unShareValP ṽ₂
    return $ us₁ :* us₂
  Shared φ ρvs (PairMV v̂₁ v̂₂) → return $ Shared φ ρvs v̂₁ :* Shared φ ρvs v̂₂
  _ → abort

viewSumUnShare ∷ UnShare → FailT IM (UnShare ∧ UnShare ∧ UnShare)
viewSumUnShare = \case
  NotShared (LV ṽ) → do
    us ← lift $ unShareValP ṽ
    return $ (NotShared $ BaseV $ BoolBV True) :* us :* (NotShared DefaultV)
  NotShared (RV ṽ) → do
    us ← lift $ unShareValP ṽ
    return $ (NotShared $ BaseV $ BoolBV False) :* (NotShared DefaultV) :* us
  Shared φ ρvs (SumMV sh v̂ₗ v̂ᵣ) → return $ Shared φ ρvs (BaseMV sh) :* Shared φ ρvs v̂ₗ :* Shared φ ρvs v̂ᵣ
  _ → abort

viewNilUnShare ∷ UnShare → FailT IM ()
viewNilUnShare = \case
  NotShared NilV → return ()
  Shared _φ _ρvs NilMV → return ()
  _ → abort

viewConsUnShare ∷ UnShare → FailT IM (UnShare ∧ UnShare)
viewConsUnShare = \case
  NotShared (ConsV ṽ₁ ṽ₂) → do
    us₁ ← lift $ unShareValP ṽ₁
    us₂ ← lift $ unShareValP ṽ₂
    return $ us₁ :* us₂
  Shared φ ρvs (ConsMV v̂₁ v̂₂) → return $ Shared φ ρvs v̂₁ :* Shared φ ρvs v̂₂
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
