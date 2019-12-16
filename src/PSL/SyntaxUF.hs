module PSL.SyntaxUF where

import UVMHS
import AddToUVMHS

----------
-- Kind --
----------

-- κ ∈ kind ⩴  …
type Kind = Annotated FullContext KindI
data KindI =
    TypeK  -- ☆   /  type
  | PrinK  -- ℙ   /  prin
  | PrinsK -- ℙs  /  prins
  deriving (Eq,Ord,Show)
makePrettySum ''KindI

----------
-- Prin --
----------

-- ρ ∈ prin ≈ 𝕏
type Prin = Annotated FullContext PrinI
type PrinI = 𝕏

----------------
-- Constraint --
----------------

-- C ∈ constraint ⩴  …
type Constr = Annotated FullContext ConstrI
data ConstrI =
    SubsetC (𝐿 Prin) (𝐿 Prin) --  P ⊆ P  /  P c= P
  deriving (Eq,Ord,Show)
makePrettySum ''ConstrI

------------
-- Effect --
------------

-- η ∈ effect ⩴  …
type Effect = Annotated FullContext EffectI
data EffectI = EffectI  --  inp:P,rev:P
  { effectIInput ∷ 𝐿 Prin
  , effectIReveal ∷ 𝐿 Prin
  } deriving (Eq,Ord,Show)
makePrettySum ''EffectI
makeLenses ''EffectI

----------
-- TVar --
----------

type TVar = Annotated FullContext TVarI
type TVarI = 𝕏

----------
-- Prot --
----------

-- φ ∈ protocol ⩴  …
type Prot = Annotated FullContext ProtI
data ProtI = 
    YaoP  -- yao
  | BGWP  -- bgw
  | GMWP  -- gmw
  deriving (Eq,Ord,Show)
makePrettySum ''ProtI

----------
-- Type --
----------

-- τ ∈ type ⩴  …
type Type = Annotated FullContext TypeI
data TypeI =
    VarT TVar                            --  α                   /  α
  | UnitT                                --  𝟙                   /  unit
  | 𝔹T                                   --  𝔹                   /  bool
  | 𝕊T                                   --  𝕊                   /  string
  | ℕT (𝑂 (ℕ ∧ 𝑂 ℕ))                     --  ℕ[n.n]              /  natn.n
  | ℤT (𝑂 (ℕ ∧ 𝑂 ℕ))                     --  ℤ[n.n]              /  intn.n
  | 𝔽T ℕ                                 --  𝔽[n]                /  floatn
  | Type :+: Type                        --  τ + τ               /  τ + τ
  | Type :×: Type                        --  τ × τ               /  τ × τ
  | ListT Type                           --  list τ              /  list τ
  | Type :→: (Effect ∧ Type)             --  τ →{η} τ            /  τ ->{η} τ
  | ForallT TVar Kind (𝐿 Constr) Type    --  ∀ α:κ. [c,…,c] ⇒ τ  /  forall α:κ. [c,…,c] => τ
  | SecT Type Prin                       --  τ{P}                /  τ{P}
  | SSecT Type (𝐿 Prin)                  --  τ{ssec:P}           /  τ{ssec:P}
  | ISecT Type (𝐿 Prin)                  --  τ{isec:P}           /  τ{isec:P}
  | ShareT Type Prot (𝐿 Prin)            --  τ{φ:P}              /  τ{φ:P}
  deriving (Eq,Ord,Show)
makePrettySum ''TypeI

---------
-- Var --
---------

type Var = Annotated FullContext VarI
type VarI = 𝕏

-------------
-- Pattern --
-------------

-- ψ ∈ pat ⩴  …
type Pat = Annotated FullContext PatI
data PatI =
    VarP Var              -- x        /  x
  | BulP                  -- •        /  ()
  | LP Pat                -- L ψ      /  L ψ
  | RP Pat                -- R ψ      /  R ψ
  | TupP Pat Pat          -- ψ,ψ      /  ψ,ψ
  | NilP                  -- []       /  []
  | ConsP Pat Pat         -- ψ∷ψ      /  ψ::ψ
  | EmptyP                -- ⟨⟩       /  <>
  | BundleP Prin Pat Pat  -- ⟨ρ.ψ⟩⧺ψ  /  <ρ.ψ>++ψ
  | AscrP Pat Type        -- ψ : τ    /  ψ : τ
  | WildP                 -- _        /  _
  -- [ψ₁;…;ψₙ] ≜ ψ₁ ∷ ⋯ ∷ ψₙ ∷ []
  -- ⟨ρ₁.ψ₁;…;ρₙ.ψₙ⟩ ≜ ⟨ρ₁.ψ₁⟩ ⧺ ⋯ ⧺ ⟨ρₙ.ψₙ⟩ ⧺ ⟨⟩
  deriving (Eq,Ord,Show)
makePrettySum ''PatI

-------------------
-- Program Terms --
-------------------

-- e ∈ term ⩴  …
type Exp = Annotated FullContext ExpI
data ExpI =
    VarE Var                       -- x                     /  x
  | BoolE 𝔹                        -- b                     /  b
  | StrE 𝕊                         -- s                     /  s
  | IntE ℤ                         -- i                     /  i
  | FltE 𝔻                         -- d                     /  d
  | BulE                           -- •                     /  ()
  | IfE Exp Exp Exp                -- if e then e else e    /  if e then e else e
  | LE Exp                         -- L e                   /  L e
  | RE Exp                         -- R e                   /  R e
  | TupE Exp Exp                   -- e,e                   /  e,e
  | NilE                           -- []                    /  []
  | ConsE Exp Exp                  -- e ∷ e                 /  e :: e
  | LetTyE Var Type Exp            -- let ψ : τ in e        /  let ψ : τ in e
  | LetE Pat Exp Exp               -- let ψ = e in e        /  let ψ = e in e
  | CaseE Exp (𝐿 (Pat ∧ Exp))      -- case e {ψ→e;…;ψ→e}    /  case e {ψ->e;…;ψ->e}
  | LamE (𝑂 Var) Pat Exp           -- λ x ψ → e             /  fun x ψ → e
  | AppE Exp Exp                   -- e e                   /  e e
  | TLamE TVar Exp                 -- Λ α → e               /  abs α → e
  | TAppE Exp Type                 -- e@τ                   /  e@τ
  | SoloE Prin Exp                 -- {ρ} e                 /  {ρ} e
  | ParE (𝐿 Prin) Exp              -- {par:P} e             /  {par:P} e
  | ShareE Prot (𝐿 Prin) Exp       -- share{φ:P} e          /  share{φ:P} e
  | AccessE Exp Prin               -- e.ρ                   /  e.ρ
  | BundleE (𝐿 (Prin ∧ Exp))       -- ⟨ρ₁.eₙ;…;ρₙ.eₙ⟩       /  <ρ₁.e₁;…;ρₙ.eₙ>
  | BundleUnionE Exp Exp           -- e⧺e                   /  e++e
  | RevealE (𝐿 Prin) Exp           -- reveal{P} e           /  reveal{P} e
  | AscrE Exp Type                 -- e:τ                   /  e:τ
  | ReadE Type Exp                 -- read[τ] e             /  read[τ] e
  | InferE                         -- _                     /  _
  | HoleE                          -- ⁇                     /  ??
  | PrimE 𝕊 (𝐿 Exp)                -- prim[⊙](e,…,e)        /  𝑁/𝐴
  | TraceE Exp Exp                 -- trace e in e          /  trace e in e
  deriving (Eq,Ord,Show)
  -- [e₁;…;eₙ] ≜ e₁ ∷ ⋯ ∷ eₙ ∷ []
makePrettySum ''ExpI

buildLambda ∷ FullContext → Var → 𝐿 Pat → Exp → Exp
buildLambda c x ψs e = case ψs of
  Nil → e
  ψ :& ψs' →
    let e' = foldrOnFrom ψs' e $ \ ψ'' e'' → Annotated c $ LamE None ψ'' e''
    in Annotated c $ LamE (Some x) ψ e'

---------------
-- Top-level --
---------------

-- tl ∈ top-level ⩴  …
type TL = Annotated FullContext TLI
data TLI =
    DeclTL Var Type          -- def x : τ        /  def x : τ
  | DefnTL Var (𝐿 Pat) Exp   -- def x ψ₁ … = e   /  def x  ψ₁ … = e
  | PrinTL (𝐿 Prin)          -- principal ρ …    /  principal ρ …
  | PrimTL Var Type          -- primitive x : τ  /  primitive x : τ
  deriving (Eq,Ord)
makePrettySum ''TLI
