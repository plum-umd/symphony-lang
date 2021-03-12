module PSL.Interpreter.Pretty where

import UVMHS

import PSL.Syntax
import PSL.Interpreter.Types

levelIF,levelLAM,levelLET,levelPAR,levelUPDATE ∷ ℕ64
levelIF     = 𝕟64 10
levelLAM    = 𝕟64 10
levelLET    = 𝕟64 10
levelPAR    = 𝕟64 10
levelUPDATE = 𝕟64 15

levelCOMMA,levelASCR,levelCONS,levelREVEAL ∷ ℕ64

levelCOMMA   = 𝕟64 20
levelASCR    = 𝕟64 21
levelCONS    = 𝕟64 22
levelREVEAL  = 𝕟64 25

levelCOND,levelCOMPARE,levelARROW,levelPLUS,levelTIMES,levelEXP ∷ ℕ64
levelCOND    = 𝕟64 30
levelCOMPARE = 𝕟64 35
levelARROW   = 𝕟64 40
levelPLUS    = 𝕟64 50
levelTIMES   = 𝕟64 60
levelEXP     = 𝕟64 70

levelAPP ∷ ℕ64
levelAPP = 𝕟64 100

levelDEREF ∷ ℕ64
levelDEREF = 𝕟64 120

levelACCESS ∷ ℕ64
levelACCESS = 𝕟64 130

levelMODE ∷ ℕ64
levelMODE  = 𝕟64 200

ppBoolPSL ∷ 𝔹 → Doc
ppBoolPSL = \case
  True → ppLit "true"
  False → ppLit "false"

ppNatPSL ∷ IPrecision → ℕ → Doc
ppNatPSL p n = concat [pretty n,ppLit "n",pretty p]

ppIntPSL ∷ IPrecision → ℤ → Doc
ppIntPSL p i = concat [pretty i,pretty p]

ppFltPSL ∷ FPrecision → 𝔻 → Doc
ppFltPSL p d = concat [pretty d,pretty p]

ppListPSL ∷ 𝐿 ValP → Doc
ppListPSL = ppCollection (ppPun "[") (ppPun "]") (ppPun ";") ∘ map pretty ∘ iter

ppArrayPSL ∷ 𝕍 ValP → Doc
ppArrayPSL = ppCollection (ppPun "[|") (ppPun "|]") (ppPun ";") ∘ map pretty ∘ iter

ppISecPSL ∷ PrinVal ⇰ Val → Doc
ppISecPSL ρvs =
  ppCollection (ppPun "⟪") (ppPun "⟫") (ppPun ";") $ mapOn (iter ρvs) $ \ (ρ :* v) →
    let ppv = case asListV v of
          Some (ṽs :* m) | m ≡ Some (SecM (single ρ)) → ppListPSL ṽs
          _ → pretty v
    in concat
      [ ppAlign $ pretty ρ
      , ppSpaceIfBreak
      , ppPun "|"
      , ppSpaceIfBreak
      , ppAlign ppv
      ]

instance Pretty Prot where
  pretty = \case
    YaoP → ppBdr "yao"
    BGWP → ppBdr "bgw"
    GMWP → ppBdr "gmw"
    BGVP → ppBdr "bgv"
    SPDZP → ppBdr "spdz"
    AutoP → ppBdr "auto"

instance Pretty IPrecision where
  pretty = \case
    InfIPr → concat
      [ ppPun "#"
      , ppBdr "∞"
      ]
    FixedIPr n₁ n₂
      | (n₁ ≡ 64) ⩓ (n₂ ≡ 0) → null
      | otherwise → concat
        [ ppPun "#"
        , pretty n₁
        , if n₂ ≡ 0
             then null
             else concat
               [ ppPun "."
               , pretty n₂
               ]
        ]

instance Pretty FPrecision where
  pretty = \case
    FixedFPr n₁ n₂
      | (n₁ ≡ 11) ⩓ (n₂ ≡ 53) → null
      | otherwise → concat
        [ ppPun "#"
        , pretty n₁
        , if n₂ ≡ 0
             then null
             else concat
               [ ppPun "."
               , pretty n₂
               ]
        ]

instance Pretty Mode where
  pretty = \case
    TopM → ppBdr "⊤"
    SecM ρs → pretty ρs

instance Pretty Val where
  pretty = \case
    BoolV b → ppBoolPSL b
    StrV s → pretty s
    NatV p n → ppNatPSL p n
    IntV p i → ppIntPSL p i
    FltV p d → ppFltPSL p d
    BulV → ppCon "•"
    LV v → ppApp (ppCon "L") [pretty v]
    RV v → ppApp (ppCon "R") [pretty v]
    NilV → ppCon "[]"
    ConsV v₁ v₂ → ppInfr levelCONS (ppPun "∷") (pretty v₁) $ pretty v₂
    CloV _sxO _ψ _e _ξ → ppCon "λ<clo>"
      -- ppPre levelLAM
      --       (ppHorizontal $ concat
      --          [ single𝐼 $ ppKey "λ<clo>"
      --          , elim𝑂 null (single ∘ ppString ∘ 𝕩name) sxO
      --          , single $ pretty ψ
      --          , single $ pretty ξ
      --          ]) $
      --       pretty e
    TCloV _α _e _ξ → ppCon "Λ<clo>"
      -- ppPre levelLAM
      --       (ppHorizontal
      --          [ ppKey "Λ<clo>"
      --          , ppString $ 𝕩name α
      --          , pretty ξ
      --          ]) $
      --       pretty e
    PrinV ρe → pretty ρe
    PrinSetV ρs → pretty ρs
    LocV m ℓ → ppApp (ppCon "loc") [pretty m,pretty ℓ]
    ArrayV ṽs → ppArrayPSL ṽs
    PairV ṽ₁ ṽ₂ → ppInflF ppTight levelCOMMA (ppPun ",") (pretty ṽ₁) $ pretty ṽ₂
    DefaultV → ppPun "⊥"
    UnknownV _τ → ppPun "?"

asListVP ∷ ValP → 𝑂 (𝐿 ValP ∧ Mode)
asListVP = \case
  SSecVP ρs v → do
    ṽs :* mO ← asListV v
    case mO of
      None → return $ ṽs :* SecM ρs
      Some m → do
        guard $ m ≡ SecM ρs
        return $ ṽs :* m
  AllVP v → do
    ṽs :* mO ← asListV v
    case mO of
      None → return $ ṽs :* TopM
      Some m → do
        guard $ m ≡ TopM
        return $ ṽs :* m
  _ → abort

asListV ∷ Val → 𝑂 (𝐿 ValP ∧ 𝑂 Mode)
asListV = \case
  ConsV ṽ₁ ṽ₂ → do
    ṽs :* m ← asListVP ṽ₂
    return $ (ṽ₁ :& ṽs) :* Some m
  NilV → return $ Nil :* None
  _ → abort

instance Pretty PrinVal where
  pretty = \case
    SinglePV ρ → ppCon ρ
    AccessPV ρ n → concat [ppCon ρ,ppPun ".",pretty n]
    VirtualPV ρ → ppApp (ppCon "VIRT") [ppCon ρ]

instance Pretty PrinExpVal where
  pretty = \case
    ValPEV ρ → pretty ρ
    PowPEV ρvs → pretty ρvs
    SetPEV n ρ → concat [ppCon ρ,ppPun "[",pretty n,ppPun "]"]

instance Pretty ValP where
  pretty v₀ = case asListVP v₀ of
    Some (ṽs :* m) → case m of
      TopM → ppListPSL ṽs
      SecM ρs → ppPostF concat levelMODE (pretty ρs) $ ppListPSL ṽs
    None → case v₀ of
     SSecVP ρs v → ppPostF concat levelMODE (pretty ρs) (pretty v)
     ISecVP ρvs → ppISecPSL ρvs
     ShareVP φ ρs cv →
       ppPostF concat levelMODE
         (ppSetBotLevel $ concat
             [ ppPun "{"
             , pretty φ
             , ppPun ":"
             , concat $ inbetween (ppPun ",") $ map pretty $ iter ρs
             , ppPun "}"
             ]) $
         pretty cv
     AllVP (v ∷ Val) → pretty v

ppPreF ∷ (𝐼 Doc → Doc) → ℕ64 → Doc → Doc → Doc
ppPreF f i oM xM = ppGA $ ppLevel i $ f $ map ppAlign $ iter [oM,xM]

ppPostF ∷ (𝐼 Doc → Doc) → ℕ64 → Doc → Doc → Doc
ppPostF f i oM xM = ppGA $ ppLevel i $ f $ map ppAlign $ iter [xM,oM]

ppInflF ∷ (𝐼 Doc → Doc) → ℕ64 → Doc → Doc → Doc → Doc
ppInflF f i oM x₁M x₂M = ppGA $ ppLevel i $ f $ map ppAlign $ iter [x₁M,oM,ppBump x₂M]

ppTight ∷ (ToIter Doc t) ⇒ t → Doc
ppTight = ppGroup ∘ concat ∘ inbetween ppNewlineIfBreak ∘ iter
