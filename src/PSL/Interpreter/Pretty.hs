module PSL.Interpreter.Pretty where

import UVMHS

import PSL.Parser
import PSL.Interpreter.Types

-- instance Pretty Val where
--   pretty = \case
--     BoolV b → pretty b
--     StrV s → pretty s
--     NatV _ n → pretty n
--     IntV _ i → pretty i
--     FltV _ d → pretty d
--     BulV → ppCon "•"
--     LV v → ppApp (ppCon "L") [pretty v]
--     RV v → ppApp (ppCon "R") [pretty v]
--     PairV v₁ v₂ → ppInfl levelCOMMA (ppPun ",") (pretty v₁) $ pretty v₂
--     NilV → ppCon "[]"
--     ConsV v₁ v₂ → ppInfr levelCONS (ppPun "∷") (pretty v₁) $ pretty v₂
--     CloV sxO ψ e _ξ → 
--       ppPre levelLAM 
--             (ppHorizontal $ concat 
--                [ single $ ppKey "λ<clo>"
--                , elim𝑂 null (ppString ∘ 𝕩name) sxO
--                , pretty ξ
--                ]) $
--             pretty e
--     TCloV α e _ξ →
--       ppPre levelLAM
--             (ppHorizontal $ concat
--                [ single $ ppKey "Λ<clo>"
--                , 𝕩name α
--                ]) $
--             pretty e
--     PrinV ρe → _
--     PrinSetV ρs → _
