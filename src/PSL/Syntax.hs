module PSL.Syntax where

import UVMHS
-- import AddToUVMHS

----------
-- Kind --
----------

-- κ ∈ kind ⩴  …
data Kind =
    TypeK  -- ☆   /  type
  | PrinK  -- ℙ   /  prin
  | PrinsK -- ℙs  /  prins
  deriving (Eq,Ord,Show)
makePrettySum ''Kind

----------
-- Prin --
----------

-- ρ ∈ prin ≈ 𝕊
type Prin = 𝕊

data PrinVal =
    SinglePV Prin
  | AccessPV Prin ℕ
  | VirtualPV Prin
  deriving (Eq,Ord,Show)
    
data PrinExpVal =
    ValPEV PrinVal
  | PowPEV (𝑃 PrinVal)
  | SetPEV ℕ Prin
  deriving (Eq,Ord,Show)

data PrinExp =
    VarPE 𝕏
  | AccessPE 𝕏 ℕ
  | StarPE 𝕏
  | ThisPE
  deriving (Eq,Ord,Show)
makePrettySum ''PrinExp

data PrinDecl =
    SinglePD Prin
  | ArrayPD Prin ℕ
  deriving (Eq,Ord,Show)
makePrettySum ''PrinDecl

data PrinKind =
    SinglePK
  | SetPK ℕ
  | VirtualPK
  deriving (Eq,Ord,Show)
makePrettySum ''PrinKind

----------------
-- Constraint --
----------------

-- C ∈ constraint ⩴  …
data Constr =
    SubsetC (𝐿 PrinExp) (𝐿 PrinExp) --  P ⊆ P  /  P c= P
  deriving (Eq,Ord,Show)
makePrettySum ''Constr

----------
-- Mode --
----------

data Mode =
    SecM (𝑃 PrinVal)
  | TopM
  deriving (Eq,Ord,Show)
makePrisms ''Mode

instance POrd Mode where 
  _ ⊑ TopM = True
  -- SecM ρ₁ ⊑ SecM ρ₂ | ρ₁ ≡ ρ₂ = True
  -- SecM ρ₁ ⊑ PSecM ρs₂ | ρ₁ ∈ ρs₂ = True
  -- PSecM ρs₁ ⊑ SecM ρ₁ | ρs₁ ≡ single ρ₁ = True
  SecM ρs₁ ⊑ SecM ρs₂ = ρs₁ ⊆ ρs₂
  _ ⊑ _ = False

-----------------
-- Effect Mode --
-----------------

data EMode =
    SecEM (𝐿 PrinExp) -- (𝑃 PrinVal)
  -- | SSecEM (𝐿 PrinExp) -- (𝑃 PrinVal)
  | TopEM
  deriving (Eq,Ord,Show)
makePrettySum ''EMode
makePrisms ''EMode

-- instance Top EMode where top = TopEM
-- instance Join EMode where
--   PSecEM ρs₁ ⊔ PSecEM ρs₂ = PSecEM $ ρs₁ ⧺ ρs₂
--   PSecEM ρs₁ ⊔ SSecEM ρs₂ = PSecEM $ ρs₁ ⧺ ρs₂
--   SSecEM ρs₁ ⊔ PSecEM ρs₂ = PSecEM $ ρs₁ ⧺ ρs₂
--   SSecEM ρs₁ ⊔ SSecEM ρs₂ = SSecEM $ ρs₁ ⧺ ρs₂
--   _ ⊔ _ = TopEM

------------
-- Effect --
------------

-- η ∈ effect ⩴  …
data Effect = Effect  
  --  inp:P,rev:P
  { effectInput ∷ 𝑃 PrinExp
  , effectReveal ∷ 𝑃 PrinExp
  , effectMode ∷ EMode
  } deriving (Eq,Ord,Show)
makePrettySum ''Effect
makeLenses ''Effect

-- instance Null Effect where null = Effect pø pø TopEM
-- instance Append Effect where
--   Effect ei₁ er₁ em₁ ⧺ Effect ei₂ er₂ em₂ = Effect (ei₁ ∪ ei₂) (er₁ ∪ er₂) $ em₁ ⊔ em₂
-- instance Monoid Effect

-- instance POrd Effect where
--   Effect ei₁ er₁ em₁ ⊑ Effect ei₂ er₂ em₂ = (ei₁ ⊆ ei₂) ⩓ (er₁ ⊆ er₂) ⩓ (em₁ ⊑ em₂)

----------
-- TVar --
----------

type TVar = 𝕏

----------
-- Prot --
----------

-- φ ∈ protocol ⩴  …
data Prot = 
    YaoP  -- yao
  | BGWP  -- bgw
  | GMWP  -- gmw
  | BGVP  -- bgv
  | SPDZP -- spdz
  | AutoP -- auto
  deriving (Eq,Ord,Show)

---------------
-- Precision --
---------------

data IPrecision =
    InfIPr
  | FixedIPr ℕ ℕ -- whole number precision, and decimal precision
  deriving (Eq,Ord,Show)

iprDefault ∷ IPrecision
iprDefault = FixedIPr 64 0

data FPrecision = 
    FixedFPr ℕ ℕ
  deriving (Eq,Ord,Show)

fprDefault ∷ FPrecision
fprDefault = FixedFPr 11 53

----------
-- Type --
----------

-- τ ∈ type ⩴  …
data Type =
    VarT TVar                                   --  α                          /  α
  | UnitT                                       --  𝟙                          /  unit
  | 𝔹T                                          --  𝔹                          /  bool
  | 𝕊T                                          --  𝕊                          /  string
  | ℙT                                          --  ℙ                          /  prin
  | ℙsT                                         --  ℙs                         /  prins
  | ℕT IPrecision                               --  ℕ#n.n                      /  nat#n.n
  | ℤT IPrecision                               --  ℤ#n.n                      /  int#n.n
  | 𝔽T FPrecision                               --  𝔽#n                        /  float#n
  | Type :+: Type                               --  τ + τ                      /  τ + τ
  | Type :×: Type                               --  τ × τ                      /  τ * τ
  | ListT Type                                  --  list τ                     /  list τ
  | Type :→: (Effect ∧ Type)                    --  τ →{η} τ                   /  τ ->{η} τ
  | (𝕏 ∧ Type ∧ 𝐿 Constr) :→†: (Effect ∧ Type)  --  (x : τ | c,…,c) →{η} τ     /  (x : τ | c,…,c) ->{η} τ
  | ForallT (𝐿 (TVar ∧ Kind)) (𝐿 Constr) Type   --  ∀ α:κ,…,α:κ | c,…,c. τ     /  forall α:κ,…,α:κ | c,…,c. τ
  | SecT (𝐿 PrinExp) Type                       --  τ{P}                       /  τ{P}
  -- | SSecT (𝐿 PrinExp) Type                      --  τ{ssec:P}                  /  τ{ssec:P}
  | ISecT (𝐿 PrinExp) Type                      --  τ{bundle:P}                /  τ{bundle:P}
  | ShareT Prot (𝐿 PrinExp) Type                --  τ{φ:P}                     /  τ{φ:P}
  | NizkTestT (𝐿 PrinExp) Type                  --  nizk-test{P} τ             /  nizk-test{P} τ
  | NizkVerifyT (𝐿 PrinExp) Type                --  nizk-verify{P} τ           /  nizk-verify{P} τ
  deriving (Eq,Ord,Show)
makePrettySum ''Type

---------
-- Var --
---------

type Var = 𝕏

-------------
-- Pattern --
-------------

-- ψ ∈ pat ⩴  …
data Pat =
    VarP Var              -- x        /  x
  | BulP                  -- •        /  ()
  | LP Pat                -- L ψ      /  L ψ
  | RP Pat                -- R ψ      /  R ψ
  | TupP Pat Pat          -- ψ,ψ      /  ψ,ψ
  | NilP                  -- []       /  []
  | ConsP Pat Pat         -- ψ∷ψ      /  ψ::ψ
  | EmptyP                -- ⟪⟫       /  <<>>
  | BundleP 𝕏 Pat Pat     -- ⟪ρ|ψ⟫⧺ψ  /  <<ρ|ψ>>++ψ
  | EmptySetP             -- {}       /  {}
  | SetP 𝕏 Pat            -- {ρ}∪ψ    /  {ρ}\/ψ
  | AscrP Pat Type        -- ψ : τ    /  ψ : τ
  | WildP                 -- _        /  _
  -- [ψ₁;…;ψₙ] ≜ ψ₁ ∷ ⋯ ∷ ψₙ ∷ []
  -- ⟨ρ₁.ψ₁;…;ρₙ.ψₙ⟩ ≜ ⟨ρ₁.ψ₁⟩ ⧺ ⋯ ⧺ ⟨ρₙ.ψₙ⟩ ⧺ ⟨⟩
  deriving (Eq,Ord,Show)
makePrettySum ''Pat
makePrisms ''Pat

--------------------------
-- Primitive Operations --
--------------------------

data Op = 
    OrO
  | AndO
  | NotO
  | PlusO
  | MinusO
  | TimesO
  | ExpO
  | DivO
  | ModO 
  | EqO
  | LTO
  | GTO
  | LTEO
  | GTEO
  | CondO
  | AbsO
  | SqrtO
  | LogO
  | NatO IPrecision
  | IntO IPrecision
  | FltO FPrecision
  | CeilO IPrecision
  deriving (Eq,Ord,Show)
makePrettySum ''Op
makePrisms ''Op

-------------------
-- Program Terms --
-------------------

-- e ∈ term ⩴  …
type Exp = Annotated FullContext ExpR
data ExpR =
    VarE Var                                 -- x                       /  x
  | BoolE 𝔹                                  -- b                       /  b
  | StrE 𝕊                                   -- s                       /  s
  | NatE IPrecision ℕ                        -- n#n.n                   /  n#n.n
  | IntE IPrecision ℤ                        -- i#n.n                   /  i#n.n
  | FltE FPrecision 𝔻                        -- d#n                     /  d#n
  | BulE                                     -- •                       /  ()
  | IfE Exp Exp Exp                          -- if e then e else e      /  if e then e else e
  | MuxIfE Exp Exp Exp                       -- mux if e then e else e  /  mux if e then e else e
  | LE Exp                                   -- L e                     /  L e
  | RE Exp                                   -- R e                     /  R e
  | TupE Exp Exp                             -- e,e                     /  e,e
  | NilE                                     -- []                      /  []
  | ConsE Exp Exp                            -- e ∷ e                   /  e :: e
  | LetTyE Pat Exp                           -- let ψ : τ in e          /  let ψ : τ in e
  | LetE Pat Exp Exp                         -- let ψ = e in e          /  let ψ = e in e
  | CaseE Exp (𝐿 (Pat ∧ Exp))                -- case e {ψ→e;…;ψ→e}      /  case e {ψ->e;…;ψ->e}
  | MuxCaseE Exp (𝐿 (Pat ∧ Exp))             -- mux case e {ψ→e;…;ψ→e}  /  mux case e {ψ->e;…;ψ->e}
  | LamE (𝑂 Var) (𝐿 Pat) Exp                 -- λ [x] ψ…ψ → e           /  fun [x] ψ…ψ → e
  | AppE Exp Exp                             -- e e                     /  e e
  | TLamE TVar Exp                           -- Λ α → e                 /  abs α → e
  | TAppE Exp Type                           -- e@τ                     /  e@τ
  | ParE (𝐿 PrinExp) Exp                     -- par {P} e               /  par {P} e
  | ShareE Prot (𝐿 PrinExp) (𝐿 PrinExp) Exp  -- share{φ:P→P} e          /  share{φ:P->P} e
  | AccessE Exp PrinExp                      -- e@ρ                     /  e@ρ
  | BundleE (𝐿 (PrinExp ∧ Exp))              -- ⟪ρ|e;…;ρ|e⟫             /  <<ρ|e;…;ρ|e>>
  | BundleUnionE Exp Exp                     -- e⧺e                     /  e++e
  | RevealE (𝐿 PrinExp) Exp                  -- reveal {P} e            /  reveal{P} e
  | SendE (𝐿 PrinExp) (𝐿 PrinExp) Exp        -- send {P→P} e            /  send{P->P} e
  | AscrE Exp Type                           -- e:τ                     /  e:τ
  | ReadE Type Exp                           -- read τ e                /  read τ e
  | WriteE Exp Exp                           -- write e                 /  write e
  | RandE Type                               -- rand τ                  /  rand τ
  | RandRangeE Type Exp                      -- rand-range τ e          /  rand-range τ e
  | InferE                                   -- _                       /  _
  | HoleE                                    -- ⁇                       /  ??
  | PrimE Op (𝐿 Exp)                         -- prim[⊙](e,…,e)          /  prim[⊙](e,…,e)
  | TraceE Exp Exp                           -- trace e in e            /  trace e in e
  | SetE (𝐿 PrinExp)                         -- {P}                     /  {P}
  | RefE Exp                                 -- ref e                   /  ref e
  | RefReadE Exp                             -- !e                      /  !e
  | RefWriteE Exp Exp                        -- e ≔ e                   /  e := e
  | ArrayE Exp Exp                           -- array[e] e              /  array[e] e
  | ArrayReadE Exp Exp                       -- e.e                     /  e.e
  | ArrayWriteE Exp Exp                      -- e ← e                   /  e <- e
  | SizeE Exp                                -- size e                  /  size e
  | DefaultE                                 -- ⊥                       /  _|_
  | ProcE Exp                                -- proc e                  /  proc e
  | ReturnE Exp                              -- return e                /  return e
  | NizkWitnessE Prot (𝐿 PrinExp) Exp        -- nizk-witness{φ:P} e     /  nizk-witness{φ:P} e
  | NizkCommitE Prot (𝐿 PrinExp) Exp         -- nizk-commit{φ:P} e      /  nizk-commit{φ:P} e
  | StringConcatE Exp Exp                    -- e ⧻ e                   /  e +++ e
  | ToStringE Exp                            -- str e                   /  str e
  deriving (Eq,Ord,Show)
  -- [e₁;…;eₙ] ≜ e₁ ∷ ⋯ ∷ eₙ ∷ []
makePrettySum ''ExpR

buildLambda ∷ FullContext → Var → 𝐿 Pat → Exp → Exp
buildLambda c x ψs e 
  | ψs ≡ Nil = e
  | otherwise = Annotated c $ LamE (Some x) ψs e

buildUnfixedLambda ∷ FullContext → Var → 𝐿 Pat → Exp → Exp
buildUnfixedLambda c x ψs e 
  | ψs ≡ Nil = e
  | otherwise = Annotated c $ LamE None (VarP x :& ψs) e

---------------
-- Top-level --
---------------

-- tl ∈ top-level ⩴  …
type TL = Annotated FullContext TLR
data TLR =
    DeclTL 𝔹 Var Type               -- def [sec] x : τ            /  def [sec] x : τ
  | DefnTL 𝔹 Var (𝐿 Pat) Exp        -- def [sec] x ψ₁ … = e       /  def [sec] x  ψ₁ … = e
  | PrinTL (𝐿 PrinDecl)             -- principal ρ …              /  principal ρ …
  | PrimTL Var Type                 -- primitive x : τ            /  primitive x : τ
  | ImportTL 𝕊 (𝐿 (𝕊 ∧ 𝐿 PrinExp))  -- import s with [x = {P}] …  /  import s with [x = {P}] …
  | VirtualPartyTL (𝐿 𝕊)            -- virtual party x            /  virtual party x
  deriving (Eq,Ord)
makePrettySum ''TLR
