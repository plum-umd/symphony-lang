module Symphony.Interpreter.Seq.Types where

import Symphony.Prelude

import Symphony.Lang.Syntax

import Symphony.Interpreter.Types
import Symphony.Interpreter.BaseVal
import Symphony.Interpreter.Pretty

data SeqVal =
    Located Mode SeqValR
  | Unknown

instance Pretty SeqVal where
  pretty = \case
    Located m v → ppPostF concat levelMODE (pretty m) $ pretty v
    Unknown     → ppCon "⋆"

type SeqValR = ValR SeqVal ClearBaseVal
