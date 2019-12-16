module PSL.SyntaxIR where

import UVMHS

import qualified PSL.SyntaxUF as UF

class Strip uf ir | uf→ir where
  strip ∷ uf → ir
instance (Strip a b) ⇒ Strip (Annotated t a) b where strip = strip ∘ annotatedElem
instance {-# OVERLAPPABLE #-} (a ~ b) ⇒ Strip a b where strip = id

----------
-- Kind --
----------

data Kind = TypeK | PrinK | PrinsK
  deriving (Eq,Ord,Show)
makePrettySum ''Kind

instance Strip UF.KindI Kind where
  strip = \case
    UF.TypeK → TypeK
    UF.PrinK → PrinK
    UF.PrinsK → PrinsK

----------
-- Prin --
----------

type Prin = 𝕏

----------
-- TVar --
----------

type TVar = 𝕏

----------
-- Prot --
----------

data Prot = YaoP | BGWP | GMWP
  deriving (Eq,Ord,Show)
makePrettySum ''Prot

instance Strip UF.ProtI Prot where
  strip = \case
    UF.YaoP → YaoP
    UF.BGWP → BGWP
    UF.GMWP → GMWP

------------
-- Effect --
------------

data Effect = Effect
  { effectInput ∷ 𝑃 𝕏
  , effectReveal ∷ 𝑃 𝕏
  } deriving (Eq,Ord,Show)
makePrettySum ''Effect
makeLenses ''Effect

instance Strip UF.EffectI Effect where
  strip (UF.EffectI is rs) = Effect (pow $ map strip is) $ pow $ map strip rs

instance Null Effect where null = Effect pø pø
instance Append Effect where
  Effect ips₁ rps₁ ⧺ Effect ips₂ rps₂ = Effect (ips₁ ∪ ips₂) (rps₁ ∪ rps₂)
instance Monoid Effect

instance POrd Effect where 
  Effect is₁ rs₁ ⊑ Effect is₂ rs₂ = (is₁ ⊆ is₂) ⩓ (rs₁ ⊆ rs₂)

----------------
-- Constraint --
----------------

-- C ∈ constraint ⩴  …
data Constr =
    SubsetC (𝑃 Prin) (𝑃 Prin) --  P ⊆ P  /  P c= P
  deriving (Eq,Ord,Show)
makePrettySum ''Constr

instance Strip UF.ConstrI Constr where
  strip = \case
    UF.SubsetC lhs rhs → SubsetC (pow $ map strip lhs) $ pow $ map strip rhs

----------
-- Type --
----------

data Type =
    VarT TVar
  | UnitT
  | 𝔹T
  | 𝕊T
  | ℕT (𝑂 (ℕ ∧ 𝑂 ℕ))
  | ℤT (𝑂 (ℕ ∧ 𝑂 ℕ))
  | 𝔽T ℕ
  | Type :+: Type
  | Type :×: Type
  | ListT Type
  | Type :→: (Effect ∧ Type)
  | ForallT TVar Kind (𝑃 Constr) Type
  | SecT Type Prin
  | SSecT Type (𝑃 Prin)
  | ISecT Type (𝑃 Prin)
  | ShareT Type Prot (𝑃 Prin)
  deriving (Eq,Ord,Show)
makePrettySum ''Type

instance Strip UF.TypeI Type where
  strip = \case
    UF.VarT x → VarT $ strip x
    UF.UnitT → UnitT
    UF.𝔹T → 𝔹T
    UF.𝕊T → 𝕊T
    UF.ℕT n → ℕT n
    UF.ℤT n → ℤT n
    UF.𝔽T n → 𝔽T n
    τ₁ UF.:+: τ₂ → strip τ₁ :+: strip τ₂
    τ₁ UF.:×: τ₂ → strip τ₁ :×: strip τ₂
    UF.ListT τ → ListT $ strip τ
    τ₁ UF.:→: (η :* τ₂) → strip τ₁ :→: (strip η :* strip τ₂)
    UF.ForallT α κ cs τ → ForallT (strip α) (strip κ) (pow $ map strip cs) $ strip τ
    UF.SecT τ ρ → SecT (strip τ) $ strip ρ
    UF.SSecT τ ρs → SSecT (strip τ) $ pow $ map strip ρs
    UF.ISecT τ ρs → ISecT (strip τ) $ pow $ map strip ρs
    UF.ShareT τ φ ρs → ShareT (strip τ) (strip φ) $ pow $ map strip ρs

---------
-- Var --
---------

type Var = 𝕏

-------------
-- Pattern --
-------------

data Pat =
    VarP Var
  | BulP
  | LP Pat
  | RP Pat
  | TupP Pat Pat
  | NilP
  | ConsP Pat Pat
  | EmptyP
  | BundleP Prin Pat Pat
  | AscrP Pat Type
  | WildP
  deriving (Eq,Ord,Show)
makePrettySum ''Pat

instance Strip UF.PatI Pat where
  strip = \case
    UF.VarP x → VarP $ strip x
    UF.BulP → BulP
    UF.LP ψ → LP $ strip ψ
    UF.RP ψ → RP $ strip ψ
    UF.TupP ψ₁ ψ₂ → TupP (strip ψ₁) $ strip ψ₂
    UF.NilP → NilP
    UF.ConsP ψ₁ ψ₂ → ConsP (strip ψ₁) $ strip ψ₂
    UF.EmptyP → EmptyP
    UF.BundleP ρ ψ₁ ψ₂ → BundleP (strip ρ) (strip ψ₁) $ strip ψ₂
    UF.AscrP ψ τ → AscrP (strip ψ) $ strip τ
    UF.WildP → WildP

-- -------------------
-- -- Program Terms --
-- -------------------
-- 
-- data Exp =
--     VarE Var
--   | BoolE 𝔹
--   | StrE 𝕊
--   | IntE ℤ
--   | FltE 𝔻
--   | BulE
--   | IfE Exp Exp Exp
--   | LE Exp
--   | RE Exp
--   | TupE Exp Exp
--   | NilE
--   | ConsE Exp Exp
--   | LetTyE Var Type Exp
--   | LetE Pat Exp Exp
--   | CaseE Exp (𝐿 (Pat ∧ Exp))
--   | LamE (𝑂 Var) Pat Exp
--   | AppE Exp Exp
--   | TLamE TVar Exp
--   | TAppE Exp Type
--   | SoloE Prin Exp
--   | ParE (𝑃 Prin) Exp
--   | ShareE Prot (𝑃 Prin) Exp
--   | AccessE Exp Prin
--   | BundleE (𝐿 (Prin ∧ Exp))
--   | BundleUnionE Exp Exp
--   | RevealE (𝐿 Prin) Exp
--   | AscrE Exp Type
--   | ReadE Type Exp
--   | InferE
--   | HoleE
--   | PrimE 𝕊 (𝐿 Exp)
--   | TraceE Exp Exp
--   deriving (Eq,Ord,Show)
-- makePrettySum ''Exp
-- 
-- ---------------
-- -- Top-level --
-- ---------------
-- 
-- data TL =
--     DefnTL Var (𝐿 Pat) Exp
--   deriving (Eq,Ord,Show)
-- makePrettySum ''TL
