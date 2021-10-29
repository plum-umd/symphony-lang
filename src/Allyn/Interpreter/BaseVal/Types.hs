module Allyn.Interpreter.BaseVal.Types where

import UVMHS

import Allyn.Syntax
import Allyn.Interpreter.Pretty

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
    NatV p n     → ppNatAllyn p n
    IntV p i     → ppIntAllyn p i
    FltV p d     → ppFltAllyn p d
    StrV s       → pretty s
    PrinV ρv     → pretty ρv
    PrinSetV ρsv → pretty ρsv

makePrisms ''BaseVal
makePrisms ''ClearBaseVal
