module PSL.Syntax where

import UVMHS
import AddToUVMHS

----------
-- Kind --
----------

-- κ ∈ kind ⩴  …
type AKind = Annotated FullContext Kind
data Kind =
    TypeK  -- ☆  /  type
  | PrinK  -- ℙ  /  prin
  deriving (Eq,Ord,Show)
makePrettySum ''Kind

----------
-- Prin --
----------

-- ρ ∈ prin ≜ 𝕏
type APrin = Annotated FullContext Prin
type Prin = 𝕏

--------------
-- Prin-set --
--------------

-- P ∈ prin-set ≜ ℘(Prin)
type APrins = Annotated FullContext Prins
type Prins = 𝑃 APrin

------------
-- Scheme --
------------

-- σ ∈ scheme ⩴  …
type AScheme = Annotated FullContext Scheme
data Scheme = 
    NoS      -- nshare
  | GMWS     -- gshare
  | YaoS     -- yshare
  | ShamirS  -- sshare
  deriving (Eq,Ord,Show)
makePrettySum ''Scheme

-----------------
-- Circuit Ops --
-----------------

-- ς ∈ circuit-ops ⩴  …
type ACirOps = Annotated FullContext CirOps
data CirOps = 
    NoCO     -- ncir
  | BoolCO   -- bcir
  | ArithCO  -- acir
  | CompCO   -- ccir
  | UnivCO   -- ucir
  deriving (Eq,Ord,Show)
makePrettySum ''CirOps

----------------
-- Constraint --
----------------

-- C ∈ constraint ⩴  …
type AConstr = Annotated FullContext Constr
data Constr =
    SubsetC APrins APrins
  deriving (Eq,Ord,Show)
makePrettySum ''Constr

----------
-- Type --
----------

-- τ ∈ type ⩴  …
type AType = Annotated FullContext Type
data Type =
    VarT 𝕏                             -- α                   /  α
  | UnitT                              -- 𝟙                   /  unit
  | 𝔹T                                 -- 𝔹                   /  bool
  | 𝕊T                                 -- 𝕊                   /  string
  | ℕT (𝑂 (ℕ ∧ 𝑂 ℕ))                   -- ℕn.n                /  natn.n
  | ℤT (𝑂 (ℕ ∧ 𝑂 ℕ))                   -- ℤn.n                /  intn.n
  | 𝔽T ℕ                               -- 𝔽n                  /  floatn
  | AType :+: AType                    -- τ + τ               /  τ + τ
  | AType :×: AType                    -- τ × τ               /  τ × τ
  | ListT AType                        -- list τ              /  list τ
  | AType :→: AType                    -- τ → τ               /  τ -> τ
  | ForallT 𝕏 AKind (𝐿 AConstr) AType  -- ∀ α:κ. [c,…,c] ⇒ τ  /  forall α:κ. [c,…,c] => τ
  | SSecT AType APrins                 -- τ{sec:P}            /  τ{sec:P}
  | ISecT AType APrins                 -- τ{par:P}            /  τ{par:P}
  | CirT AType ACirOps AScheme APrins  -- τ{ς:σ:P}            /  τ{ς:σ:P}
  | MpcT APrins AType                  -- MPC{P} τ            /  MPC{P} τ
  deriving (Eq,Ord,Show)
makePrettySum ''Type

----------
-- Prot --
----------

-- φ ∈ protocol ⩴  …
type AProt = Annotated FullContext Prot
data Prot = 
    YaoP  -- yao
  | BGWP  -- bgw
  | GMWP  -- gmw
  | NoneP -- none
  deriving (Eq,Ord,Show)
makePrettySum ''Prot

-------------
-- Pattern --
-------------

-- ψ ∈ pat ⩴  …
type APat = Annotated FullContext Pat
data Pat =
    VarP 𝕏                  -- x        /  x
  | BulP                    -- •        /  ()
  | Inj1P APat              -- ι₁ ψ     /  in1 ψ
  | Inj2P APat              -- ι₂ ψ     /  in2 ψ
  | TupP APat APat          -- ψ,ψ      /  ψ,ψ
  | NilP                    -- []       /  []
  | ConsP APat APat         -- ψ∷ψ      /  ψ::ψ
  | EmptyP                  -- ∅        /  empty
  | BundleP APat APrin APat -- ⟨ψ@α⟩⧺ψ  /  <ψ@α>++ψ
  | WildP                   -- _        /  _
  -- [ψ₁;…;ψₙ] ≜ ψ₁ ∷ ⋯ ∷ ψₙ ∷ []
  -- ⟨ψ₁@ρ₁;…;ψₙ@ρₙ⟩ ≜ ⟨ψ₁@ρ₁⟩ ⧺ ⋯ ⧺ ⟨ψₙ@ρₙ⟩ ⧺ ∅
  deriving (Eq,Ord,Show)
makePrettySum ''Pat

-------------------
-- Program Terms --
-------------------

-- e ∈ term ⩴  …
type AExp = Annotated FullContext Exp
data Exp =
    VarE 𝕏                         -- x                     /  x
  | BoolE 𝔹                        -- b                     /  b
  | StrE 𝕊                         -- s                     /  s
  | IntE ℤ                         -- i                     /  i
  | DblE 𝔻                         -- d                     /  d
  | BulE                           -- •                     /  ()
  | IfE AExp AExp AExp             -- if e then e else e    /  if e then e else e
  | Inj1E AExp                     -- ι₁ e                  /  in1 e
  | Inj2E AExp                     -- ι₂ e                  /  in2 e
  | TupE AExp AExp                 -- e,e                   /  e,e
  | NilE                           -- []                    /  []
  | ConsE AExp AExp                -- e ∷ e                 /  e :: e
  | LetTyE 𝕏 AType AExp            -- let ψ : τ in e        /  let ψ : τ in e
  | LetE APat AExp AExp            -- let ψ = e in e        /  let ψ = e in e
  | CaseE AExp (𝐿 (APat ∧ AExp))   -- case e {ψ→e;…;ψ→e}    / case e {ψ->e;…;ψ->e}
  | LamE (𝑂 𝕏) APat AExp           -- λ x ψ → e             /  fun x ψ → e
  | AppE AExp AExp                 -- e e                   /  e e
  | TLamE 𝕏 AExp                   -- Λ α → e               /  abs α → e
  | TAppE AExp AType               -- e@τ                   /  e@τ
  | SoloE APrin AExp               -- {P} e                 /  {P} e
  | ParE APrins AExp               -- par{P} e              /  par{P} e
  | CirE AExp                      -- ~e                    /  ~e
  | ShareE (𝑂 AScheme) APrins AExp -- share{σ:P} e          /  share{φ:P} e
  | EmptyE                         -- ∅                     /  empty
  | BundleOneE AExp APrin          -- ⟨e@ρ⟩                 /  <e@ρ>
  | BundleUnionE AExp AExp         -- e⧺e                   /  e++e
  | BundleSetE (𝐿 (APrin ∧ AExp))  -- ⟨P⇒e,…,P⇒e⟩           /  <P=>e,…,P=>e>
  | BundleAccessE AExp APrin       -- e.P                   /  e.P
  | MPCE AProt APrins AExp         -- mpc{φ:P} e            /  mpc{φ:P} e
  | RevealE APrins AExp            -- reveal{P} e           /  mpc{φ:P} e
  | ReturnE AExp                   -- return e              /  return e
  | BindE APat AExp AExp           -- ψ ← e₁ ; e₂           /  ψ <- e₁ ; e₂
  | PrimE 𝕊 (𝐿 AExp)               -- prim[⊙](e,…,e)        /  𝑁/𝐴
  | AscrE AExp AType               -- e:τ                   /  e:τ
  | ReadE AType                    -- read[τ]               /  read[τ]
  | HoleE                          -- _                     /  _
  deriving (Eq,Ord,Show)
  -- [e₁;…;eₙ] ≜ e₁ ∷ ⋯ ∷ eₙ ∷ []
  -- ⟨e₁@ρ₁;…;eₙ@ρₙ⟩ ≜ ⟨e₁@ρ₁⟩ ⧺ ⋯ ⧺ ⟨eₙ@ρₙ⟩
makePrettySum ''Exp

---------------
-- Top-level --
---------------

-- s ∈ top-level ⩴  …
type ATL = Annotated FullContext TL
data TL =
    DeclTL 𝕏 AType            -- def x : τ        /  def x : τ
  | DefnTL 𝕏 AExp             -- def x = e        /  def x = e
  | PrinTL APrin              -- principal ρ      /  principal ρ
  | TrustTL APrins            -- trust P          /  trust P
  | SecurityTL APrins APrins  -- security P ⫫ P   /  security P _||_ P
  | PrimTL 𝕏 AType            -- primitive x : τ  /  primitive x : τ
  deriving (Eq,Ord)
makePrettySum ''TL

