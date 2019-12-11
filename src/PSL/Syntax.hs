module PSL.Syntax where

import UVMHS

----------
-- Kind --
----------

-- κ ∈ kind ⩴  …
type AKind = Annotated FullContext Kind
data Kind =
    TypeK  -- ☆   /  type
  | PrinK  -- ℙ   /  prin
  | PrinsK -- ℙs  /  prins
  deriving (Eq,Ord,Show)
makePrettySum ''Kind

----------
-- Prin --
----------

-- ρ ∈ prin ≈ 𝕏
type APrin = Annotated FullContext Prin
type Prin = 𝕏

--------------
-- Prin-set --
--------------

-- P ∈ prin ≜ ℘(Prin)
type APrins = Annotated FullContext Prins
type Prins = 𝑃 APrin

extractPrins ∷ APrins → 𝑃 Prin
extractPrins = pow ∘ map extract ∘ iter ∘ extract

----------------
-- Constraint --
----------------

-- C ∈ constraint ⩴  …
type AConstr = Annotated FullContext Constr
data Constr =
    SubsetC APrins APrins --  P ⊆ P  /  P c= P
  deriving (Eq,Ord,Show)
makePrettySum ''Constr

------------
-- Effect --
------------

-- η ∈ effect ⩴  …
type AEffect = Annotated FullContext Effect
data Effect =
    Effect APrins APrins  --  inp:P,rev:P
  deriving (Eq,Ord,Show)
makePrettySum ''Effect

----------
-- TVar --
----------

type ATVar = Annotated FullContext TVar
type TVar = 𝕏

----------
-- Prot --
----------

-- φ ∈ protocol ⩴  …
type AProt = Annotated FullContext Prot
data Prot = 
    YaoP  -- yao
  | BGWP  -- bgw
  | GMWP  -- gmw
  deriving (Eq,Ord,Show)
makePrettySum ''Prot

----------
-- Type --
----------

-- τ ∈ type ⩴  …
type AType = Annotated FullContext Type
data Type =
    VarT ATVar                             --  α                   /  α
  | UnitT                                  --  𝟙                   /  unit
  | 𝔹T                                     --  𝔹                   /  bool
  | 𝕊T                                     --  𝕊                   /  string
  | ℕT (𝑂 (ℕ ∧ 𝑂 ℕ))                       --  ℕ[n.n]              /  natn.n
  | ℤT (𝑂 (ℕ ∧ 𝑂 ℕ))                       --  ℤ[n.n]              /  intn.n
  | 𝔽T ℕ                                   --  𝔽[n]                /  floatn
  | AType :+: AType                        --  τ + τ               /  τ + τ
  | AType :×: AType                        --  τ × τ               /  τ × τ
  | ListT AType                            --  list τ              /  list τ
  | AType :→: (AEffect ∧ AType)            --  τ →{η} τ            /  τ ->{η} τ
  | ForallT ATVar AKind (𝐿 AConstr) AType  --  ∀ α:κ. [c,…,c] ⇒ τ  /  forall α:κ. [c,…,c] => τ
  | SecT AType APrin                       --  τ{P}                /  τ{P}
  | SSecT AType APrins                     --  τ{ssec:P}           /  τ{ssec:P}
  | ISecT AType APrins                     --  τ{isec:P}           /  τ{isec:P}
  | MPCT AType AProt APrins                --  τ{mpc:φ:P}          /  τ{mpc:φ:P}
  deriving (Eq,Ord,Show)
makePrettySum ''Type

---------
-- Var --
---------

type AVar = Annotated FullContext Var
type Var = 𝕏

-------------
-- Pattern --
-------------

-- ψ ∈ pat ⩴  …
type APat = Annotated FullContext Pat
data Pat =
    VarP AVar               -- x        /  x
  | BulP                    -- •        /  ()
  | LP APat                 -- L ψ      /  L ψ
  | RP APat                 -- R ψ      /  R ψ
  | TupP APat APat          -- ψ,ψ      /  ψ,ψ
  | NilP                    -- []       /  []
  | ConsP APat APat         -- ψ∷ψ      /  ψ::ψ
  | EmptyP                  -- ⟨⟩       /  <>
  | BundleP APrin APat APat -- ⟨ρ.ψ⟩⧺ψ  /  <ρ.ψ>++ψ
  | AscrP APat AType        -- ψ : τ    /  ψ : τ
  | WildP                   -- _        /  _
  -- [ψ₁;…;ψₙ] ≜ ψ₁ ∷ ⋯ ∷ ψₙ ∷ []
  -- ⟨ρ₁.ψ₁;…;ρₙ.ψₙ⟩ ≜ ⟨ρ₁.ψ₁⟩ ⧺ ⋯ ⧺ ⟨ρₙ.ψₙ⟩ ⧺ ⟨⟩
  deriving (Eq,Ord,Show)
makePrettySum ''Pat

-------------------
-- Program Terms --
-------------------

-- e ∈ term ⩴  …
type AExp = Annotated FullContext Exp
data Exp =
    VarE AVar                      -- x                     /  x
  | BoolE 𝔹                        -- b                     /  b
  | StrE 𝕊                         -- s                     /  s
  | IntE ℤ                         -- i                     /  i
  | FltE 𝔻                         -- d                     /  d
  | BulE                           -- •                     /  ()
  | IfE AExp AExp AExp             -- if e then e else e    /  if e then e else e
  | LE AExp                        -- L e                   /  L e
  | RE AExp                        -- R e                   /  R e
  | TupE AExp AExp                 -- e,e                   /  e,e
  | NilE                           -- []                    /  []
  | ConsE AExp AExp                -- e ∷ e                 /  e :: e
  | LetTyE AVar AType AExp         -- let ψ : τ in e        /  let ψ : τ in e
  | LetE APat AExp AExp            -- let ψ = e in e        /  let ψ = e in e
  | CaseE AExp (𝐿 (APat ∧ AExp))   -- case e {ψ→e;…;ψ→e}    /  case e {ψ->e;…;ψ->e}
  | LamE (𝑂 AVar) APat AExp        -- λ x ψ → e             /  fun x ψ → e
  | AppE AExp AExp                 -- e e                   /  e e
  | TLamE ATVar AExp               -- Λ α → e               /  abs α → e
  | TAppE AExp AType               -- e@τ                   /  e@τ
  | SoloE APrin AExp               -- {ρ} e                 /  {ρ} e
  | ParE APrins AExp               -- {par:P} e             /  {par:P} e
  | ShareE AProt APrins AExp       -- share{φ:P} e          /  share{φ:P} e
  | AccessE AExp APrin             -- e.ρ                   /  e.ρ
  | BundleE (𝐿 (APrin ∧ AExp))     -- ⟨ρ₁.eₙ;…;ρₙ.eₙ⟩       /  <ρ₁.e₁;…;ρₙ.eₙ>
  | BundleUnionE AExp AExp         -- e⧺e                   /  e++e
  | RevealE APrins AExp            -- reveal{P} e           /  reveal{P} e
  | AscrE AExp AType               -- e:τ                   /  e:τ
  | ReadE AType AExp               -- read[τ] e             /  read[τ] e
  | InferE                         -- _                     /  _
  | HoleE                          -- ⁇                     /  ??
  | PrimE 𝕊 (𝐿 AExp)               -- prim[⊙](e,…,e)        /  𝑁/𝐴
  | TraceE AExp AExp               -- trace e in e          / trace e in e
  deriving (Eq,Ord,Show)
  -- [e₁;…;eₙ] ≜ e₁ ∷ ⋯ ∷ eₙ ∷ []
makePrettySum ''Exp

---------------
-- Top-level --
---------------

-- s ∈ top-level ⩴  …
type ATL = Annotated FullContext TL
data TL =
    DeclTL AVar AEffect AType  -- def x :{η} τ     /  def x :{η} τ
  | DefnTL AVar (𝐿 APat) AExp  -- def x ψ₁ … = e   /  def x  ψ₁ … = e
  | PrinTL (𝐿 APrin)           -- principal ρ …    /  principal ρ …
  | TrustTL APrins             -- trust P          /  trust P
  | SecurityTL APrins APrins   -- security P ⫫ P   /  security P _||_ P
  | PrimTL AVar AType          -- primitive x : τ  /  primitive x : τ
  deriving (Eq,Ord)
makePrettySum ''TL

