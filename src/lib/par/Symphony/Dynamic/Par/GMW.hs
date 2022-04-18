module Symphony.Dynamic.Par.GMW where

import Symphony.Prelude

import Symphony.Lang.Syntax

type GmwSession = ()
type Gmw = ()

primGmw ∷ GmwSession → Op → 𝐿 Gmw → IO Gmw
primGmw π op sh = undefined
