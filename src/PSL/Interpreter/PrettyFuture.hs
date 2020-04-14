module PSL.Interpreter.PrettyFuture where

{-
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

ppListPSL ∷ 𝐿 ValP → Doc
ppListPSL = ppCollection (ppPun "[") (ppPun "]") (ppPun ";") ∘ map pretty ∘ iter

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

instance Pretty Val where
  pretty = \case
    BoolV b → pretty b
    StrV s → pretty s
    NatV p n → concat 
      [ pretty n
      , ppLit "n"
      , pretty p
      ]
    IntV p i → concat [pretty i,pretty p]
    FltV _ d → ppApp (ppCon "flt") [pretty d]
    BulV → ppCon "•"
    LV v → ppApp (ppCon "L") [pretty v]
    RV v → ppApp (ppCon "R") [pretty v]
    -- PairV v₁ v₂ → ppInfl levelCOMMA (ppPun ",") (pretty v₁) $ pretty v₂
    NilV → ppCon "[]"
    ConsV v₁ v₂ → ppInfr levelCONS (ppPun "∷") (pretty v₁) $ pretty v₂
    CloV _sxO _ψ _e _ξ → 
      ppKey "λ<clo>"
      -- ppPre levelLAM 
      --       (ppHorizontal $ concat 
      --          [ single𝐼 $ ppKey "λ<clo>"
      --          , elim𝑂 null (single ∘ ppString ∘ 𝕩name) sxO
      --          , single $ pretty ψ
      --          , single $ pretty ξ
      --          ]) $
      --       pretty e
    TCloV α e ξ →
      ppPre levelLAM
            (ppHorizontal 
               [ ppKey "Λ<clo>"
               , ppString $ 𝕩name α
               , pretty ξ
               ]) $
            pretty e
    PrinV ρe → pretty ρe
    PrinSetV ρs → pretty ρs
    LocV m ℓ → ppApp (ppCon "loc") [pretty m,pretty ℓ]
    ArrayV ṽs → pretty ṽs
    PairV ṽ₁ ṽ₂ → ppInfl levelCOMMA (ppPun ",") (pretty ṽ₁) $ pretty ṽ₂
    DefaultV → ppPun "⊥"
    NizkVerifyV ρs v → ppApp (ppCon "nizk-verify") [pretty ρs,pretty v]

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
    AccessPV ρ n → concat
      [ ppLit ρ
      , ppPun "."
      , pretty n
      ]

instance Pretty ValP where
  pretty v₀ = case asListVP v₀ of
    Some (ṽs :* m) → case m of
      TopM → ppListPSL ṽs
      SecM ρs → ppPostF concat levelMODE (pretty ρs) $ ppListPSL ṽs
    None → case v₀ of
     SSecVP ρs v → ppPostF concat levelMODE (pretty ρs) (pretty v)
     ISecVP ρvs → ppISecPSL ρvs
     ShareVP zk φ ρs vmpc → 
       ppApp (ppOp $ if zk then "nizk-witness" else "share") 
         [ concat
             [ ppPun "{"
             , pretty φ
             , ppPun ":"
             , concat $ inbetween (ppPun ",") $ map pretty $ iter ρs
             , ppPun "}"
             ]
          , pretty vmpc
          ]
     AllVP (v ∷ Val) → pretty v
     UnknownVP → ppCon "unknown" 
     PairVP (ṽ₁ ∷ ValP) (ṽ₂ ∷ ValP) → ppInflF ppTight levelCOMMA (ppPun ",") (pretty ṽ₁) $ pretty ṽ₂

instance Pretty ValMPC where
  pretty = \case
    BaseMV ℕ BaseValMPC
    PairMV ValMPC ValMPC
    SumMV ℕ 𝔹 ValMPC ValMPC
    NilMV
    ConsMV ValMPC ValMPC
    DefaultMV

instance Pretty BaseValMPC where

ppPreF ∷ (𝐼 Doc → Doc) → ℕ64 → Doc → Doc → Doc
ppPreF f i oM xM = ppGA $ ppLevel i $ f $ map ppAlign $ iter [oM,xM]

ppPostF ∷ (𝐼 Doc → Doc) → ℕ64 → Doc → Doc → Doc
ppPostF f i oM xM = ppGA $ ppLevel i $ f $ map ppAlign $ iter [xM,oM]

ppInflF ∷ (𝐼 Doc → Doc) → ℕ64 → Doc → Doc → Doc → Doc
ppInflF f i oM x₁M x₂M = ppGA $ ppLevel i $ f $ map ppAlign $ iter [x₁M,oM,ppBump x₂M]

ppTight ∷ (ToIter Doc t) ⇒ t → Doc
ppTight = ppGroup ∘ concat ∘ inbetween ppNewlineIfBreak ∘ iter
-}
