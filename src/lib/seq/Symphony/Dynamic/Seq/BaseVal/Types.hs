module Symphony.Dynamic.Seq.BaseVal.Types where

import Symphony.Prelude

import Symphony.Lang.Syntax
import Symphony.Lang.Parser

data BaseVal v =
    Clear ClearBaseVal
  | Encrypted Prot (𝑃 PrinVal) v
  deriving (Eq, Ord, Show)

instance Pretty v ⇒ Pretty (BaseVal v) where
  pretty = \case
    Clear bv → pretty bv
    Encrypted φ ρvs bv →
      ppPostF concat levelMODE
      (ppSetBotLevel $ concat
       [ ppPun "{"
       , concat $ inbetween (ppPun ",") $ map pretty $ iter ρvs
       , ppPun "}"
       ]) $
      ppPostF concat levelMODE
      (ppSetBotLevel $ concat
       [ ppPun "⌈"
       , pretty φ
       , ppPun "⌉"
       ]) $
      pretty bv

data ClearBaseVal =
    BulV
  | BoolV 𝔹
  | NatV IPrecision ℕ
  | IntV IPrecision ℤ
  | FltV FPrecision 𝔻
  | StrV 𝕊
  | PrinV PrinVal
  | PrinSetV PrinSetVal
  deriving (Eq, Ord, Show)

instance Pretty ClearBaseVal where
  pretty = \case
    BulV         → ppCon "•"
    BoolV b      → pretty b
    NatV p n     → ppNatSymphony p n
    IntV p i     → ppIntSymphony p i
    FltV p d     → ppFltSymphony p d
    StrV s       → pretty s
    PrinV ρv     → pretty ρv
    PrinSetV ρsv → pretty ρsv

makePrisms ''BaseVal
makePrisms ''ClearBaseVal
