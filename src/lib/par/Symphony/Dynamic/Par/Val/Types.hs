module Symphony.Dynamic.Par.Val.Types where

import Symphony.Prelude

import Symphony.Lang.Syntax

import Symphony.Dynamic.Par.GMW.Types

data Val m =
    Known (LocVal m)
  | Unknown

data LocVal m =
    Base BaseVal
  | Product (Val m) (Val m)
  | Sum BaseVal (Val m) (Val m)
  | List (𝐿 (Val m))
  | Closure (Val m → m (Val m))
  | Reference Mode (ℝMut (Val m))
  | Vector Mode (𝕍Mut (Val m))
  | Bundle (PrinVal ⇰ (Val m))

data BaseVal =
    Unit
  | Bool BoolVal
  | Nat NatVal
  | Int IntVal
  | Str 𝕊
  | Prin PrinVal
  | PrinSet (𝑃 PrinVal)

data BoolVal =
    ClearB 𝔹
  | EncB (𝑃 PrinVal) EncBool

data EncBool =
    GmwB GmwBool

data NatVal =
    ClearN ℕ64
  | EncN (𝑃 PrinVal) EncNat

data EncNat =
    GmwN GmwNat64

data IntVal =
    ClearZ ℤ64
  | EncZ (𝑃 PrinVal) EncInt

data EncInt =
    GmwZ GmwInt64
