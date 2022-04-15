module Symphony.Dynamic.Par.Seq.Types where

import Symphony.Prelude

import Symphony.Lang.Syntax
import Symphony.Lang.Parser

import Symphony.Dynamic.Par.Types
import Symphony.Dynamic.Par.BaseVal

data SeqVal =
    Located Mode SeqValR
  | Unknown

instance Pretty SeqVal where
  pretty = \case
    Located m v → ppPostF concat levelMODE (pretty m) $ pretty v
    Unknown     → ppCon "⋆"

type SeqValR = ValR SeqVal ClearBaseVal
