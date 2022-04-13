module Symphony.Interpreter.Dist.Types where

import Symphony.Prelude

import Symphony.Syntax
import Symphony.Interpreter.Types
import Symphony.Interpreter.BaseVal
import Symphony.Interpreter.Error
import Symphony.Interpreter.Types (EMPVal)

data DistVal =
    Known DistValR
  | Unknown

instance Pretty DistVal where
  pretty = \case
    Known v → pretty v
    Unknown → ppCon "⋆"

type DistValR = ValR DistVal ExShare

--------------
--- Shares ---
--------------

data ExShare where
  ExShare ∷ ∀ p . (Protocol p) ⇒ SProt p → (Share p) → ExShare

instance Eq ExShare where
  (ExShare φˢ₁ sh₁) == (ExShare φˢ₂ sh₂) = case deq φˢ₁ φˢ₂ of
    NoDEq  → False
    YesDEq → sh₁ ≡ sh₂

instance Ord ExShare where
  compare (ExShare φˢ₁ sh₁) (ExShare φˢ₂ sh₂) = case dcmp φˢ₁ φˢ₂ of
    LTDCmp → LT
    GTDCmp → GT
    EQDCmp → compare sh₁ sh₂

deriving instance (Show ExShare)

instance Pretty ExShare where
  pretty (ExShare _φˢ sh) = pretty sh

elimExShare ∷ (Protocol p) ⇒ SProt p → ExShare → IM DistVal (Share p)
elimExShare φˢ₁ (ExShare φˢ₂ sh) = case deq φˢ₁ φˢ₂ of
  NoDEq  → throwIErrorCxt TypeIError "φˢ₁ ≢ φˢ₂" $ frhs [ ("φˢ₁", pretty φˢ₁), ("φˢ₂", pretty φˢ₂) ]
  YesDEq → return sh

---------------------
--- MPC Protocols ---
---------------------

class
  ( Eq     (Share p)
  , Ord    (Share p)
  , Show   (Share p)
  , Pretty (Share p)
  ) ⇒
  Protocol p where
    type Share p ∷ ★

    sendShare  ∷ SProt p → 𝑃 Channel → ClearBaseVal → IM DistVal ()
    recvShare  ∷ SProt p → 𝑃 PrinVal → Channel → BaseType → IM DistVal (Share p)
    embed      ∷ SProt p → 𝑃 PrinVal → ClearBaseVal → IM DistVal (Share p)
    prim       ∷ SProt p → 𝑃 PrinVal → Op → 𝐿 (Share p) → IM DistVal (Share p)
    sendReveal ∷ SProt p → 𝑃 PrinVal → Channel → Share p → IM DistVal ()
    recvReveal ∷ SProt p → 𝑃 Channel → BaseType → IM DistVal ClearBaseVal
