module PSL.Interpreter.Val where

import UVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Lens
import PSL.Interpreter.Error
import PSL.Interpreter.Share

import PSL.Interpreter.Primitives

withValP ∷ (STACK) ⇒ ValP → (Val → IM a) → (Prot → 𝑃 PrinVal → MPCVal → IM a) → IM a
withValP ṽ kVal kMPCVal = do
  m ← askL iCxtGlobalModeL
  case ṽ of
    SSecVP ρvs v → do
      guardErr (m ⊑ SecM ρvs) $
        throwIErrorCxt TypeIError "withValP: SSecVP: ¬ m ⊑ SecM ρvs " $ frhs
        [ ("m",pretty m)
        , ("ρvs",pretty ρvs)
        ]
      kVal v
    ShareVP φ ρvs v̂ → do
      guardErr (SecM ρvs ⊑ m) $
        throwIErrorCxt TypeIError "withValP: SecM ρvs ⋢ m" $ frhs
        [ ("ρvs", pretty ρvs)
        , ("m", pretty m)
        ]
      kMPCVal φ ρvs v̂
    AllVP v → kVal v
    _ → throwIErrorCxt TypeIError "withValP: ṽ ∉ {SSecVP _ _,ShareVP _ _ _,AllVP _}" $ frhs
        [ ("ṽ",pretty ṽ) ]

introValP ∷ (STACK) ⇒ Val → IM ValP
introValP v = do
  m ← askL iCxtGlobalModeL
  return $ case m of
    SecM ρs → SSecVP ρs v
    TopM → AllVP v

elimValP ∷ (STACK) ⇒ ValP → IM Val
elimValP ṽ = withValP ṽ return shareError
  where shareError = throwIErrorCxt TypeIError "elimValP: ṽ ∉ {SSecVP _ _, AllVP _}" $ frhs [ ("ṽ", pretty ṽ) ]

unShareValP ∷ (STACK) ⇒ ValP → IM UnShare
unShareValP ṽ = withValP ṽ (return ∘ NotShared) (\ φ ρvs v̂ → return $ Shared φ ρvs v̂)

reShareValP ∷ (STACK) ⇒ UnShare → IM ValP
reShareValP = \case
  NotShared v    → introValP v
  Shared φ ρvs v̂ → valPFrMPCVal v̂
    where valPFrMPCVal v̂ = case v̂ of
            DefaultMV → introValP DefaultV
            BaseMV sh → return $ ShareVP φ ρvs $ BaseMV sh
            PairMV v̂₁ v̂₂ → do
              ṽ₁ ← valPFrMPCVal v̂₁
              ṽ₂ ← valPFrMPCVal v̂₂
              introValP $ PairV ṽ₁ ṽ₂
            SumMV sh₁ v̂₂ v̂₃ → return $ ShareVP φ ρvs $ SumMV sh₁ v̂₂ v̂₃
            NilMV → introValP NilV
            ConsMV v̂₁ v̂₂ → do
              ṽ₁ ← valPFrMPCVal v̂₁
              ṽ₂ ← valPFrMPCVal v̂₂
              introValP $ ConsV ṽ₁ ṽ₂
            BulMV → introValP $ BaseV BulBV

mpcValFrValP ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → ValP → IM MPCVal
mpcValFrValP p sp ρvs₁ ṽ = withValP ṽ (mpcValFrVal p sp ρvs₁) checkProt
  where checkProt φ ρvs₂ v̂ = do
          sameProt φ sp
          if ρvs₁ ≡ ρvs₂ then
            return v̂
          else
            throwIErrorCxt TypeIError "mpcValFrValP: ρvs₁ ≢ ρvs₂" $ frhs
            [ ("ρvs₁", pretty ρvs₁)
            , ("ρvs₂", pretty ρvs₂)
            ]

mpcValFrVal ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ P p → SProt p → 𝑃 PrinVal → Val → IM MPCVal
mpcValFrVal p sp ρvs = \case
  BaseV bv → mpcValFrBaseVal bv p sp
  PairV ṽ₁ ṽ₂ → do
    v̂₁ ← mpcValFrValP ρvs ṽ₁ p sp
    v̂₂ ← mpcValFrValP ρvs ṽ₂ p sp
    return $ PairMV v̂₁ v̂₂
  LV ṽ → do
    v̂ ← mpcValFrValP ρvs ṽ p sp
    tt ← boolConst p True ≫= Share sp
    return $ SumMV tt v̂ DefaultMV
  RV ṽ → do
    v̂ ← mpcValFrValP ρvs ṽ p sp
    ff ← boolConst p False ≫= Share sp
    return $ SumMV ff DefaultMV v̂
  NilV → return NilMV
  ConsV ṽ₁ ṽ₂ → do
    v̂₁ ← mpcValFrValP ρvs ṽ₁ p sp
    v̂₂ ← mpcValFrValP ρvs ṽ₂ p sp
    return $ ConsMV v̂₁ v̂₂
  BulV → return BulMV
  UnknownV τ → throwIErrorCxt TypeIError "mpcValFrVal: UnknownV τ" $ frhs [ ("τ", pretty τ) ]
  v → throwIErrorCxt NotImplementedIError "mpcValFrVal" $ frhs
      [ ("v", pretty v) ]

mpcValFrBaseVal ∷ ∀ (p ∷ Prot). (STACK, Protocol p) ⇒ BaseVal → P p → SProt p → IM MPCVal
mpcValFrBaseVal bv p sp = case bv of
  BoolBV b → do
    pv ← boolConst p b
    return $ BaseMV $ Share sp pv
  NatBV pr n → do
    pv ← natConst p pr n
    return $ BaseMV $ Share sp pv
  IntBV pr i → do
    pv ← intConst p pr i
    return $ BaseMV $ Share sp pv
  FltBV pr f → do
    pv ← fltConst p pr f
    return $ BaseMV $ Share sp pv
  BulBV → return BulMV
  _ → throwIErrorCxt TypeIError "mpcValFrBaseVal: bv ∈ {StrBV _, PrinBV _}" $ frhs [ ("bv", pretty bv) ]

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
          NotShared v → withProt φ $ \ p sp → mpcValFrVal p sp ρvs v
          Shared _φ _ρvs v̂ → return v̂
      return $ Inr $ φ :* ρvs :* v̂s

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
      v̂' ← withProt φ $ muxMPCVal sh₁ v̂₂ v̂₃
      return $ Shared φ ρvs v̂'

muxVal ∷ (STACK) ⇒ BaseVal → Val → Val → IM Val
muxVal bv₁ v₂ v₃ = case (v₂, v₃) of
  (DefaultV, DefaultV) → return DefaultV
  (DefaultV, BaseV bv₃) → do
    let τ₂ = typeOfBaseVal bv₃
    bv₂ ← defaultBaseValOf τ₂
    bv' ← interpPrim CondO $ frhs [ bv₁, bv₂, bv₃ ]
    return $ BaseV bv'
  (BaseV bv₂, DefaultV) → do
    let τ₃ = typeOfBaseVal bv₂
    bv₃ ← defaultBaseValOf τ₃
    bv' ← interpPrim CondO $ frhs [ bv₁, bv₂, bv₃ ]
    return $ BaseV bv'
  (BaseV bv₂, BaseV bv₃) → do
    bv' ← interpPrim CondO $ frhs [ bv₁, bv₂, bv₃ ]
    return $ BaseV bv'
  (DefaultV, PairV ṽ₃ₗ ṽ₃ᵣ) → do
    ṽ₁ ← introValP $ BaseV bv₁
    ṽ₂ ← introValP DefaultV
    us₁ₗ :& us₂ₗ :& us₃ₗ :& Nil ← mapM unShareValP $ frhs [ ṽ₁, ṽ₂, ṽ₃ₗ ]
    usₗ ← muxUnShare us₁ₗ us₂ₗ us₃ₗ
    ṽₗ ← reShareValP usₗ
    us₁ᵣ :& us₂ᵣ :& us₃ᵣ :& Nil ← mapM unShareValP $ frhs [ ṽ₁, ṽ₂, ṽ₃ᵣ ]
    usᵣ ← muxUnShare us₁ᵣ us₂ᵣ us₃ᵣ
    ṽᵣ ← reShareValP usᵣ
    return $ PairV ṽₗ ṽᵣ
  (PairV ṽ₂ₗ ṽ₂ᵣ, DefaultV) → do
    ṽ₁ ← introValP $ BaseV bv₁
    ṽ₃ ← introValP DefaultV
    us₁ₗ :& us₂ₗ :& us₃ₗ :& Nil ← mapM unShareValP $ frhs [ ṽ₁, ṽ₂ₗ, ṽ₃ ]
    usₗ ← muxUnShare us₁ₗ us₂ₗ us₃ₗ
    ṽₗ ← reShareValP usₗ
    us₁ᵣ :& us₂ᵣ :& us₃ᵣ :& Nil ← mapM unShareValP $ frhs [ ṽ₁, ṽ₂ᵣ, ṽ₃ ]
    usᵣ ← muxUnShare us₁ᵣ us₂ᵣ us₃ᵣ
    ṽᵣ ← reShareValP usᵣ
    return $ PairV ṽₗ ṽᵣ
  (PairV ṽ₂ₗ ṽ₂ᵣ, PairV ṽ₃ₗ ṽ₃ᵣ) → do
    us₁ₗ :& us₂ₗ :& us₃ₗ :& Nil ← mapM unShareValP $ frhs [ ṽ₁, ṽ₂ₗ, ṽ₃ₗ ]
    usₗ ← muxUnShare us₁ₗ us₂ₗ us₃ₗ
    ṽₗ ← reShareValP usₗ
    us₁ᵣ :& us₂ᵣ :& us₃ᵣ :& Nil ← mapM unShareValP $ frhs [ ṽ₁, ṽ₂ᵣ, ṽ₃ᵣ ]
    usᵣ ← muxUnShare us₁ᵣ us₂ᵣ us₃ᵣ
    ṽᵣ ← reShareValP usᵣ
    return $ PairV ṽₗ ṽᵣ

typeOfBaseVal ∷ BaseVal → Type
typeOfBaseVal = \case
  BoolBV _b → 𝔹T
  NatBV pr _n → ℕT pr
  IntBV pr _i → ℤT pr
  FltBV pr _f → 𝔽T pr
  bv → throwIErrorCxt NotImplementedIError "typeOfBaseVal" $ frhs [ ("bv", pretty bv) ]

defaultBaseValOf ∷ (STACK) ⇒ Type → IM BaseVal
defaultBaseValOf = \case
  𝔹T → return $ BoolBV False
  ℕT pr → return $ NatBV pr 0
  ℤT pr → return $ IntBV pr 0
  𝔽T pr → return $ FltBV pr 0
  τ → throwIErrorCxt NotImplementedIError "defaultBaseValOf" $ frhs [ ("τ", pretty τ) ]



sumVal ∷ (STACK) ⇒ Val → Val → IM Val
sumVal v₁ v₂ = case (v₁, v₂) of
  (_, DefaultV) → return v₁
  (DefaultV, _) → return v₂
  (BaseV bv₁, BaseV bv₂) → do
    bv' ← interpPrim PlusO $ frhs [ bv₁, bv₂ ]
    return $ BaseV bv'
