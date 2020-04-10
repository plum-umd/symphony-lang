module PSL.Interpreter.Pretty where

import UVMHS

import PSL.Parser
import PSL.Interpreter.Types
import PSL.Interpreter.Json

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
    LocV ℓ → ppApp (ppCon "loc") [pretty ℓ]
    ArrayV ṽs → pretty ṽs
    PairV ṽ₁ ṽ₂ → pretty $ pretty ṽ₁ :* ṽ₂
    DefaultV → ppPun "⊥"
    NizkVerifyV ρs v → ppApp (ppCon "nizk-verify") [pretty ρs,pretty v]
