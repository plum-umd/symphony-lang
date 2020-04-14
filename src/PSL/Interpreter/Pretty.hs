module PSL.Interpreter.Pretty where

import UVMHS

import PSL.Interpreter.Types
import PSL.Interpreter.Json

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


instance Pretty Val where
  pretty = \case
    BoolV b → pretty b
    StrV s → pretty s
    NatV p n → ppApp (ppCon "nat") [ppString $ iprecisionSuffix p,pretty n]
    IntV p i → ppApp (ppCon "int") [ppString $ iprecisionSuffix p,pretty i]
    FltV _ d → ppApp (ppCon "ilt") [pretty d]
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
    PairV ṽ₁ ṽ₂ → pretty $ pretty ṽ₁ :* ṽ₂
    DefaultV → ppPun "⊥"
    NizkVerifyV ρs v → ppApp (ppCon "nizk-verify") [pretty ρs,pretty v]
