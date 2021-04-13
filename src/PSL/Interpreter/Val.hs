module PSL.Interpreter.Val where

import UVMHS
import AddToUVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Lens
import PSL.Interpreter.Error
import PSL.Interpreter.Share
import PSL.Interpreter.Send

import PSL.Interpreter.Primitives

import qualified Prelude as HS

--------------------
--- Public Stuff ---
--------------------

introValP ∷ (Monad m, MonadReader ICxt m, STACK) ⇒ Val → m ValP
introValP v = do
  gm ← askL iCxtGlobalModeL
  return $ SSecVP gm v

elimValP ∷ (STACK) ⇒ ValP → IM Val
elimValP ṽ = do
  v̑ ← unValP ṽ
  elimValS v̑


--

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
            UnknownV → return v
            DefaultV → return DefaultV

modeFrValP ∷ (STACK) ⇒ ValP → Mode
modeFrValP = \case
  SSecVP m _ → m
  ISecVP b → SecM $ keys b
  ShareVP _ ρvs _ → SecM $ ρvs

shareValP ∷ (STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → PrinVal → Type → ValP → IM ValP
shareValP p φ ρvs ρv τ ṽ = shareOrEmbedValP p φ ρvs (Some ρv) (Some τ) ṽ

embedValP ∷ (STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → ValP → IM ValP
embedValP p φ ρvs ṽ = shareOrEmbedValP p φ ρvs None None ṽ

revealValP ∷ (STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → PrinVal → ValP → IM ValP
revealValP p φ ρvsFr ρvTo ṽ = map (SSecVP (SecM $ single𝑃 ρvTo)) $ revealValOrMPCVal p φ ρvsFr ρvTo *$ unValS φ ρvsFr *$ unValP ṽ

sendValP ∷ (STACK) ⇒ 𝑃 PrinVal → PrinVal → ValP → IM ValP
sendValP ρvsRs ρvS ṽ = do
  lm ← askL iCxtLocalModeL
  v̑ ← unValP ṽ
  case v̑ of
    SSecVS v → case lm of
      TopM → return $ SSecVP (SecM ρvsRs) v
      SecM ρvsLM | ρvsRs ⊆ ρvsLM → return $ SSecVP (SecM ρvsRs) v
      SecM ρvsLM | ρvS ∈ ρvsLM  → do
                     eachWith (sendValNR v) $ ρvsRs ∖ (single𝑃 ρvS)
                     return $ SSecVP (SecM ρvsRs) v
      SecM _ρvsLM → do
        v ← recvValNR ρvS
        return $ SSecVP (SecM ρvsRs) v

bindVarTo ∷ (STACK) ⇒ Var → ValP → IM a → IM a
bindVarTo x ṽ = mapEnvL iCxtEnvL ((x ↦ ṽ) ⩌)

viewBul ∷ (STACK) ⇒ ValP → FailT IM ()
viewBul ṽ = do
  v̑ ← lift $ unValP ṽ
  case v̑ of
    SSecVS BulV       → return ()
    ShareVS _ _ BulMV → return ()
    _                 → abort

viewTup ∷ (STACK) ⇒ ValP → FailT IM (ValP ∧ ValP)
viewTup ṽ = do
  v̑ ← lift $ unValP ṽ
  case v̑ of
    SSecVS (PairV ṽ₁ ṽ₂) → return $ ṽ₁ :* ṽ₂
    ShareVS φ ρvs (PairMV v̂₁ v̂₂) → return $ ShareVP φ ρvs v̂₁ :* ShareVP φ ρvs v̂₂
    _ → abort

viewNil ∷ (STACK) ⇒ ValP → FailT IM ()
viewNil ṽ = do
  v̑ ← lift $ unValP ṽ
  case v̑ of
    SSecVS NilV       → return ()
    ShareVS _ _ NilMV → return ()
    _                 → abort

viewCons ∷ (STACK) ⇒ ValP → FailT IM (ValP ∧ ValP)
viewCons ṽ = do
  v̑ ← lift $ unValP ṽ
  case v̑ of
    SSecVS (ConsV ṽ₁ ṽ₂) → return $ ṽ₁ :* ṽ₂
    ShareVS φ ρvs (ConsMV v̂₁ v̂₂) → return $ ShareVP φ ρvs v̂₁ :* ShareVP φ ρvs v̂₂
    _ → abort

bindPatValP ∷ (STACK) ⇒ Pat → ValP → FailT IM (IM ValP → IM ValP)
bindPatValP ψ ṽ = case ψ of
  VarP x → return $ bindVarTo x ṽ
  BulP → do
    viewBul ṽ
    return id
  TupP ψ₁ ψ₂ → do
    ṽ₁ :* ṽ₂ ← viewTup ṽ
    f₁ ← bindPatValP ψ₁ ṽ₁
    f₂ ← bindPatValP ψ₂ ṽ₂
    return $ compose [f₁, f₂]
  LP ψ' → do
    v̑ ← lift $ unValP ṽ
    case v̑ of
      SSecVS v → do
        ṽ' ← abort𝑂 $ view lVL v
        bindPatValP ψ' ṽ'
      ShareVS φ ρvs (SumMV pv₁ v̂₂ _v̂₃) → do
        ṽ₁ ← reValP $ reValS φ ρvs $ Inr $ BaseMV pv₁
        ṽ₂ ← reValP $ reValS φ ρvs $ Inr v̂₂
        f  ← bindPatValP ψ' ṽ₂
        return $ \ xM → do
          ṽb ← mapEnvL iCxtMPCPathConditionL (ṽ₁ :&) $ f xM
          ṽd ← introValP DefaultV
          muxValP ṽ₁ ṽb ṽd
  RP ψ' → do
    v̑ ← lift $ unValP ṽ
    case v̑ of
      SSecVS v → do
        ṽ' ← abort𝑂 $ view rVL v
        bindPatValP ψ' ṽ'
      ShareVS φ ρvs (SumMV pv₁ _v̂₂ v̂₃) → do
        ṽ₁ ← reValP $ reValS φ ρvs $ Inr $ BaseMV pv₁
        ṽ₃ ← reValP $ reValS φ ρvs $ Inr v̂₃
        f  ← bindPatValP ψ' ṽ₃
        return $ \ xM → do
          negṽ₁ ← notValP ṽ₁
          ṽb ← mapEnvL iCxtMPCPathConditionL (negṽ₁ :&) $ f xM
          ṽd ← introValP DefaultV
          muxValP ṽ₁ ṽd ṽb
  NilP → do
    viewNil ṽ
    return id
  ConsP ψ₁ ψ₂ → do
    ṽ₁ :* ṽ₂ ← viewCons ṽ
    f₁ ← bindPatValP ψ₁ ṽ₁
    f₂ ← bindPatValP ψ₂ ṽ₂
    return $ compose [f₁, f₂]
  EmptyP → do
    ρvs ← abort𝑂 $ view iSecVPL ṽ
    guard $ count ρvs ≡ 0
    return id
  BundleP ρx ψ₁ ψ₂ → do
    ρvs ← abort𝑂 $ view iSecVPL ṽ
    ρ :* v :* ρvs' ← abort𝑂 $ dminView ρvs
    ρv ← lift $ introValP $ PrinV $ ValPEV ρ
    let f₁ = bindVarTo ρx ρv
    f₂ ← bindPatValP ψ₁ $ SSecVP (SecM $ single ρ) v
    f₃ ← bindPatValP ψ₂ $ ISecVP ρvs'
    return $ f₃ ∘ f₂ ∘ f₁
  EmptySetP → do
    v ← lift $ elimValP ṽ
    guard $ v ≡ PrinSetV pø
    return id
  SetP x ψ' → do
    v ← lift $ elimValP ṽ
    ρvs ← abort𝑂 $ view prinSetVL v
    ρ :* ρs ← abort𝑂 $ pmin ρvs
    ρv ← lift $ introValP $ PrinV $ ValPEV ρ
    ρvs' ← lift $ introValP $ PrinSetV ρs
    let f₁ = bindVarTo x ρv
    f₂ ← bindPatValP ψ' ρvs'
    return $ f₂ ∘ f₁
  AscrP ψ' _τ → bindPatValP ψ' ṽ
  WildP → return id
  _ → throwIErrorCxt NotImplementedIError "bindPatValP: pattern ψ not implemented" $ frhs [ ("ψ", pretty ψ) ]

notValP ∷ (STACK) ⇒ ValP → IM ValP
notValP ṽ = primValP NotO $ frhs [ ṽ ]

primValP ∷ (STACK) ⇒ Op → 𝐿 ValP → IM ValP
primValP op = withShareInfo (primVals op) (primMPCVals op)

muxValP ∷ (STACK) ⇒ ValP → ValP → ValP → IM ValP
muxValP ṽ₁ ṽ₂ ṽ₃ = withShareInfo kMuxVals kMuxMPCVals $ frhs [ ṽ₁, ṽ₂, ṽ₃ ]
  where kMuxVals vs = do
          v₁ :* v₂ :* v₃ ← fromSomeCxt $ view three𝐿L vs
          bv₁ ← error𝑂 (view baseVL v₁) $ throwIErrorCxt TypeIError "bad" empty𝐿
          introValP *$ muxVal bv₁ v₂ v₃
        kMuxMPCVals p φ ρvs v̂s = do
          v̂₁ :* v̂₂ :* v̂₃ ← fromSomeCxt $ view three𝐿L v̂s
          pv₁ ← error𝑂 (view baseMVL v̂₁) $ throwIErrorCxt TypeIError "bad" empty𝐿
          reValP *$ map ((reValS φ ρvs) ∘ Inr) $ muxMPCVal p ρvs pv₁ v̂₂ v̂₃

sumValP ∷ (STACK) ⇒ ValP → ValP → IM ValP
sumValP ṽ₁ ṽ₂ = withShareInfo kSumVals kSumMPCVals $ frhs [ ṽ₁, ṽ₂ ]
  where kSumVals vs = do
          v₁ :* v₂ ← fromSomeCxt $ view two𝐿L vs
          introValP *$ sumVal v₁ v₂
        kSumMPCVals p φ ρvs v̂s = do
          v̂₁ :* v̂₂ ← fromSomeCxt $ view two𝐿L v̂s
          reValP *$ map ((reValS φ ρvs) ∘ Inr) $ sumMPCVal p ρvs v̂₁ v̂₂

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

unValP ∷ (Monad m, MonadReader ICxt m, MonadError IError m, STACK) ⇒ ValP → m ValS
unValP ṽ = do
  gm ← askL iCxtGlobalModeL
  case ṽ of
    SSecVP m v → do
      -- (1) All parties executing this code must have the value (gm ⊑ m)
      guardErr (gm ⊑ m) $
        throwIErrorCxt TypeIError "unValP: SSecVP: gm ⋢ m " $ frhs
        [ ("ṽ", pretty ṽ)
        , ("gm",pretty gm)
        , ("m",pretty m)
        ]
      return $ SSecVS v
    ISecVP b → do
      let m = SecM $ keys b
      -- (1) All parties executing this code must have a value (gm ⊑ m)
      guardErr (gm ⊑ m) $
        throwIErrorCxt TypeIError "unValP: ISecVP: gm ⋢ m " $ frhs
        [ ("gm",pretty gm)
        , ("m",pretty m)
        ]
      return $ ISecVS b
    ShareVP φ ρvs v̂ → do
      -- (1) All parties executing this code must have the value (gm ⊑ SecM ρvs) AND
      -- (2) All parties that have the value (i.e. the parties amongst whom the value is shared) must be executing this code (SecM ρvs ⊑ gm)
      guardErr (gm ≡ SecM ρvs) $
        throwIErrorCxt TypeIError "unValP: gm ≢ SecM ρvs" $ frhs
        [ ("gm", pretty gm)
        , ("ρvs", pretty ρvs)
        ]
      return $ ShareVS φ ρvs v̂

reValP ∷ (Monad m, MonadReader ICxt m, STACK) ⇒ ValS → m ValP
reValP = \case
  SSecVS v → introValP v
  ISecVS b → return $ ISecVP b
  ShareVS φ ρvs v̂ → case v̂ of
    DefaultMV → return $ SSecVP (SecM ρvs) DefaultV
    BulMV → return $ SSecVP (SecM ρvs) BulV
    BaseMV _ → return $ ShareVP φ ρvs v̂
    PairMV v̂₁ v̂₂ → do
      ṽ₁ ← reValP $ ShareVS φ ρvs v̂₁
      ṽ₂ ← reValP $ ShareVS φ ρvs v̂₂
      return $ SSecVP (SecM ρvs) $ PairV ṽ₁ ṽ₂
    SumMV _ _ _ → return $ ShareVP φ ρvs v̂
    NilMV → return $ SSecVP (SecM ρvs) NilV
    ConsMV v̂₁ v̂₂ → do
      ṽ₁ ← reValP $ ShareVS φ ρvs v̂₁
      ṽ₂ ← reValP $ ShareVS φ ρvs v̂₂
      return $ SSecVP (SecM ρvs) $ ConsV ṽ₁ ṽ₂

unValS ∷ (Monad m, MonadReader ICxt m, MonadError IError m, STACK) ⇒ SProt p → 𝑃 PrinVal → ValS → m (Val ∨ MPCVal p)
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

elimValS ∷ (Monad m, MonadReader ICxt m, MonadError IError m, STACK) ⇒ ValS → m Val
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

shareOrEmbedValP ∷ (STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → 𝑂 PrinVal → 𝑂 Type → ValP → IM ValP
shareOrEmbedValP p φ ρvs oρv oτ ṽ = reValP *$ map (ShareVS φ ρvs) $ shareOrEmbed p φ ρvs oρv oτ *$ unValS φ ρvs *$ unValP ṽ

shareOrEmbed ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m, STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → 𝑂 PrinVal → 𝑂 Type → (Val ∨ MPCVal p) → m (MPCVal p)
shareOrEmbed p φ ρvs oρv oτ vorv̂ = case vorv̂ of
  Inl v → case v of
    DefaultV → return DefaultMV
    BulV     → return BulMV
    BaseV bv → map BaseMV $ case oρv of
      None    → embedBaseVal p ρvs bv
      Some ρv → shareBaseVal p ρv ρvs bv
    PairV ṽ₁ ṽ₂ → do
      oτ₁ :* oτ₂ ← case oτ of
        None             → return $ None :* None
        Some (τ₁ :×: τ₂) → return $ Some τ₁ :* Some τ₂
        Some τ           → throwIErrorCxt SyntaxIError "shareOrEmbedVal: type τ is inconsistent with PairV" $ frhs [ ("τ", pretty τ) ]
      v̂₁ ← shareOrEmbedR oτ₁ *$ unValSR *$ unValP ṽ₁
      v̂₂ ← shareOrEmbedR oτ₂ *$ unValSR *$ unValP ṽ₂
      return $ PairMV v̂₁ v̂₂
    LV ṽ → do
      oτ₁ ← case oτ of
        None            → return $ None
        Some (τ₁ :+: _) → return $ Some τ₁
        Some τ          → throwIErrorCxt SyntaxIError "shareOrEmbedVal: type τ is inconsistent with LV" $ frhs [ ("τ", pretty τ) ]
      v̂  ← shareOrEmbedR oτ₁ *$ unValSR *$ unValP ṽ
      tt ← case oρv of
        None    → embedBaseVal p ρvs $ BoolBV True
        Some ρv → shareBaseVal p ρv ρvs $ BoolBV True
      return $ SumMV tt v̂ DefaultMV
    RV ṽ → do
      oτ₂ ← case oτ of
        None            → return $ None
        Some (_ :+: τ₂) → return $ Some τ₂
        Some τ          → throwIErrorCxt SyntaxIError "shareOrEmbedVal: type τ is inconsistent with RV" $ frhs [ ("τ", pretty τ) ]
      v̂  ← shareOrEmbedR oτ₂ *$ unValSR *$ unValP ṽ
      ff ← case oρv of
        None    → embedBaseVal p ρvs $ BoolBV False
        Some ρv → shareBaseVal p ρv ρvs $ BoolBV False
      return $ SumMV ff DefaultMV v̂
    NilV → return NilMV
    ConsV ṽ₁ ṽ₂ → do
      oτ₁ :* oτ₂ ← case oτ of
        None           → return $ None :* None
        Some (ListT τ) → return $ Some τ :* Some (ListT τ)
        Some τ         → throwIErrorCxt SyntaxIError "shareOrEmbedVal: type τ is inconsistent with ConsV" $ frhs [ ("τ", pretty τ) ]
      v̂₁ ← shareOrEmbedR oτ₁ *$ unValSR *$ unValP ṽ₁
      v̂₂ ← shareOrEmbedR oτ₂ *$ unValSR *$ unValP ṽ₂
      return $ ConsMV v̂₁ v̂₂
    UnknownV → do
      τ  ← fromSomeCxt oτ
      ρv ← error𝑂 oρv $ throwIErrorCxt TypeIError "shareOrEmbedVal: unknown of type τ cannot be embedded" $ frhs [ ("τ", pretty τ) ]
      shareUnknown p ρvs ρv τ
    _ → throwIErrorCxt TypeIError "shareOrEmbedVal: value v cannot be shared or embedded" $ frhs [ ("v", pretty v) ]
  Inr v̂ → return v̂
  where shareOrEmbedR = shareOrEmbed p φ ρvs oρv
        unValSR       = unValS φ ρvs

shareUnknown ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m, STACK, Protocol p) ⇒ P p → 𝑃 PrinVal → PrinVal → Type → m (MPCVal p)
shareUnknown p ρvs ρv τ = case τ of
  UnitT → return BulMV
  BaseT bτ → do
    pv ← shareUnk p ρv ρvs bτ
    return $ BaseMV pv
  τ₁ :×: τ₂ → do
    v̂₁ ← shareUnknownR τ₁
    v̂₂ ← shareUnknownR τ₂
    return $ PairMV v̂₁ v̂₂
  τ₁ :+: τ₂ → do
    tag ← shareUnk p ρv ρvs 𝔹T
    v̂₁ ← shareUnknownR τ₁
    v̂₂ ← shareUnknownR τ₂
    return $ SumMV tag v̂₁ v̂₂
  _ → throwIErrorCxt TypeIError "shareUnknown: unknown of type τ cannot be shared" $ frhs [ ("τ", pretty τ) ]
  where shareUnknownR = shareUnknown p ρvs ρv

revealValOrMPCVal ∷ (STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → PrinVal → (Val ∨ MPCVal p) → IM Val
revealValOrMPCVal p φ ρvsFr ρvTo = \case
  Inl v → revealVal p φ ρvsFr ρvTo v
  Inr v̂ → reveal p ρvsFr ρvTo v̂

revealVal ∷ (STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → PrinVal → Val → IM Val
revealVal p φ ρvsFr ρvTo v = case v of
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
  where revealValPR = revealValP p φ ρvsFr ρvTo

withShareInfo ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m, STACK) ⇒
                (𝐿 Val → m a) → (∀ p. (Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → 𝐿 (MPCVal p) → m a) → 𝐿 ValP → m a
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
      v̂s ← mapM (shareOrEmbed p φ ρvs None None) vorv̂s
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

muxVal ∷ (STACK) ⇒ BaseVal → Val → Val → IM Val
muxVal bv₁ v₂ v₃ = case (v₂, v₃) of
  (DefaultV, DefaultV) → return DefaultV
  (DefaultV, BulV) → return BulV
  (BulV, DefaultV) → return BulV
  (BulV, BulV) → return BulV
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
    ṽd ← introValP DefaultV
    muxSum False ṽd ṽd True ṽ₃ ṽd
  (LV ṽ₂, DefaultV) → do
    ṽd ← introValP DefaultV
    muxSum True ṽ₂ ṽd False ṽd ṽd
  (DefaultV, RV ṽ₃) → do
    ṽd ← introValP DefaultV
    muxSum False ṽd ṽd False ṽd ṽ₃
  (RV ṽ₂, DefaultV) → do
    ṽd ← introValP DefaultV
    muxSum False ṽd ṽ₂ False ṽd ṽd
  (LV ṽ₂, LV ṽ₃) → do
    ṽd ← introValP DefaultV
    muxSum True ṽ₂ ṽd True ṽ₃ ṽd
  (RV ṽ₂, RV ṽ₃) → do
    ṽd ← introValP DefaultV
    muxSum False ṽd ṽ₂ False ṽd ṽ₃
  (LV ṽ₂, RV ṽ₃) → do
    ṽd ← introValP DefaultV
    muxSum True ṽ₂ ṽd False ṽd ṽ₃
  (RV ṽ₂, LV ṽ₃) → do
    ṽd ← introValP DefaultV
    muxSum False ṽd ṽ₂ True ṽ₃ ṽd
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
          ṽₗ ← muxValP ṽ₁ ṽ₂ₗ ṽ₃ₗ
          ṽᵣ ← muxValP ṽ₁ ṽ₂ᵣ ṽ₃ᵣ
          return $ constr ṽₗ ṽᵣ
        muxSum tag₂ ṽ₂ₗ ṽ₂ᵣ tag₃ ṽ₃ₗ ṽ₃ᵣ = do
          ṽ₁  ← introValP $ BaseV bv₁
          tag ← (interpPrim CondO $ frhs [ bv₁, BoolBV tag₂, BoolBV tag₃ ]) ≫= fromSomeCxt ∘ (view boolBVL)
          if tag
            then do
            ṽ' ← muxValP ṽ₁ ṽ₂ₗ ṽ₃ₗ
            return $ LV ṽ'
            else do
            ṽ' ← muxValP ṽ₁ ṽ₂ᵣ ṽ₃ᵣ
            return $ RV ṽ'

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
  (DefaultMV, PairMV v̂₃ₗ v̂₃ᵣ) → muxTup DefaultMV DefaultMV v̂₃ₗ v̂₃ᵣ PairMV
  (PairMV v̂₂ₗ v̂₂ᵣ, DefaultMV) → muxTup v̂₂ₗ v̂₂ᵣ DefaultMV DefaultMV PairMV
  (PairMV v̂₂ₗ v̂₂ᵣ, PairMV v̂₃ₗ v̂₃ᵣ) → muxTup v̂₂ₗ v̂₂ᵣ v̂₃ₗ v̂₃ᵣ PairMV
  (DefaultMV, SumMV pv₃ v̂₃ₗ v̂₃ᵣ) → do
    pv₂ ← embedBaseVal p ρvs (BoolBV False)
    muxSum pv₂ DefaultMV DefaultMV pv₃ v̂₃ₗ v̂₃ᵣ
  (SumMV pv₂ v̂₂ₗ v̂₂ᵣ, DefaultMV) → do
    pv₃ ← embedBaseVal p ρvs (BoolBV False)
    muxSum pv₂ v̂₂ₗ v̂₂ᵣ pv₃ DefaultMV DefaultMV
  (SumMV pv₂ v̂₂ₗ v̂₂ᵣ, SumMV pv₃ v̂₃ₗ v̂₃ᵣ) → muxSum pv₂ v̂₂ₗ v̂₂ᵣ pv₃ v̂₃ₗ v̂₃ᵣ
  (NilMV, NilMV) → return NilMV
  (DefaultMV, ConsMV v̂₃ₗ v̂₃ᵣ) → muxTup DefaultMV DefaultMV v̂₃ₗ v̂₃ᵣ ConsMV
  (ConsMV v̂₂ₗ v̂₂ᵣ, DefaultMV) → muxTup v̂₂ₗ v̂₂ᵣ DefaultMV DefaultMV ConsMV
  (ConsMV v̂₂ₗ v̂₂ᵣ, ConsMV v̂₃ₗ v̂₃ᵣ) → muxTup v̂₂ₗ v̂₂ᵣ v̂₃ₗ v̂₃ᵣ ConsMV
  _ → throwIErrorCxt TypeIError "muxMPCVal: MPC values v̂₂ and v̂₃ have different shapes." $ frhs
      [ ("v̂₂", pretty v̂₂)
      , ("v̂₃", pretty v̂₃)
      ]
  where muxTup v̂₂ₗ v̂₂ᵣ v̂₃ₗ v̂₃ᵣ constr = do
          v̂ₗ ← muxMPCVal p ρvs pv₁ v̂₂ₗ v̂₃ₗ
          v̂ᵣ ← muxMPCVal p ρvs pv₁ v̂₂ᵣ v̂₃ᵣ
          return $ constr v̂ₗ v̂ᵣ
        muxSum pv₂ v̂₂ₗ v̂₂ᵣ pv₃ v̂₃ₗ v̂₃ᵣ = do
          tag ← exePrim p ρvs CondO $ frhs [ pv₁, pv₂, pv₃ ]
          v̂ₗ ← muxMPCVal p ρvs pv₁ v̂₂ₗ v̂₃ₗ
          v̂ᵣ ← muxMPCVal p ρvs pv₁ v̂₂ᵣ v̂₃ᵣ
          return $ SumMV tag v̂ₗ v̂ᵣ

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
          ṽₗ ← sumValP ṽ₁ₗ ṽ₂ₗ
          ṽᵣ ← sumValP ṽ₁ᵣ ṽ₂ᵣ
          return $ constr ṽₗ ṽᵣ
        sumSum tag₁ ṽ₁ tag₂ ṽ₂ = do
          tag ← (interpPrim PlusO $ frhs [ BoolBV tag₁, BoolBV tag₂ ]) ≫= fromSomeCxt ∘ (view boolBVL)
          ṽ ← sumValP ṽ₁ ṽ₂
          return $ if tag then LV ṽ else RV ṽ

sumMPCVal ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ P p → 𝑃 PrinVal → MPCVal p → MPCVal p → IM (MPCVal p)
sumMPCVal p ρvs v̂₁ v̂₂ = case (v̂₁, v̂₂) of
  (DefaultMV, _) → return v̂₂
  (_, DefaultMV) → return v̂₁
  (BulMV, BulMV) → return BulMV
  (BaseMV pv₁, BaseMV pv₂) → do
    pv' ← exePrim p ρvs PlusO $ frhs [ pv₁, pv₂ ]
    return $ BaseMV pv'
  (PairMV v̂₁ₗ v̂₁ᵣ, PairMV v̂₂ₗ v̂₂ᵣ) → sumTup v̂₁ₗ v̂₁ᵣ v̂₂ₗ v̂₂ᵣ PairMV
  (SumMV pv₁ v̂₁ₗ v̂₁ᵣ, SumMV pv₂ v̂₂ₗ v̂₂ᵣ) → sumSum pv₁ v̂₁ₗ v̂₁ᵣ pv₂ v̂₂ₗ v̂₂ᵣ
  (NilMV, NilMV) → return NilMV
  (ConsMV v̂₁ₗ v̂₁ᵣ, ConsMV v̂₂ₗ v̂₂ᵣ) → sumTup v̂₁ₗ v̂₁ᵣ v̂₂ₗ v̂₂ᵣ ConsMV
  _ → throwIErrorCxt TypeIError "sumMPCVal: MPC values v̂₁ and v̂₂ have different shapes." $ frhs
      [ ("v̂₁", pretty v̂₁)
      , ("v̂₂", pretty v̂₂)
      ]
  where sumTup v̂₁ₗ v̂₁ᵣ v̂₂ₗ v̂₂ᵣ constr = do
          v̂ₗ ← sumMPCVal p ρvs v̂₁ₗ v̂₂ₗ
          v̂ᵣ ← sumMPCVal p ρvs v̂₁ᵣ v̂₂ᵣ
          return $ constr v̂ₗ v̂ᵣ
        sumSum pv₁ v̂₁ₗ v̂₁ᵣ pv₂ v̂₂ₗ v̂₂ᵣ = do
          tag ← exePrim p ρvs PlusO $ frhs [ pv₁, pv₂ ]
          v̂ₗ ← sumMPCVal p ρvs v̂₁ₗ v̂₂ₗ
          v̂ᵣ ← sumMPCVal p ρvs v̂₁ᵣ v̂₂ᵣ
          return $ SumMV tag v̂ₗ v̂ᵣ
