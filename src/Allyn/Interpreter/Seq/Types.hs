module Allyn.Interpreter.Seq.Types where

import UVMHS

import Allyn.Syntax
import Allyn.Interpreter.Types
import Allyn.Interpreter.BaseVal
import Allyn.Interpreter.Pretty

data SeqVal =
    Located Mode SeqValR
  | Unknown

instance Pretty SeqVal where
  pretty = \case
    Located m v → ppPostF concat levelMODE (pretty m) $ pretty v
    Unknown     → ppCon "⋆"

type SeqValR = ValR SeqVal ClearBaseVal
