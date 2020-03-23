module PSL.Interpreter.Pretty where

import UVMHS

import PSL.Parser
import PSL.Interpreter.Types

instance Pretty Val where
  pretty = \case
    BoolV b → pretty b
    StrV s → pretty s
    NatV _ n → pretty n
    IntV _ i → pretty i
    FltV _ d → pretty d
    BulV → ppCon "•"
    LV v → ppApp (ppCon "L") [pretty v]
    RV v → ppApp (ppCon "R") [pretty v]
    PairV v₁ v₂ → ppInfl levelCOMMA (ppPun ",") (pretty v₁) $ pretty v₂
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
