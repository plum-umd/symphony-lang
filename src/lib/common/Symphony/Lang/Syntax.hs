module Symphony.Lang.Syntax where

import Symphony.Prelude

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

---------------
-- Principal --
---------------

-- ρ ∈ prin ≈ 𝕊
type Prin = 𝕊

data PrinVal =
    SinglePV Prin
  | AccessPV Prin ℕ
  deriving (Eq, Ord, Show)

instance Pretty PrinVal where
  pretty = \case
    SinglePV ρ → ppCon ρ
    AccessPV ρ n → concat [ppCon ρ,ppPun ".",pretty n]

data PrinSetVal =
    PowPSV (𝑃 PrinVal)
  | ArrPSV Prin ℕ
  deriving (Eq, Ord, Show)

instance Pretty PrinSetVal where
  pretty = \case
    PowPSV ρvs → pretty ρvs
    ArrPSV ρ n → concat [ppCon ρ, ppPun "[", pretty n, ppPun "]"]

data PrinExp =
    VarPE 𝕏
  | AccessPE 𝕏 ℕ
  deriving (Eq, Ord, Show)

data PrinSetExp =
    VarPSE 𝕏
  | PowPSE (𝐿 PrinExp)
  | ThisPSE
  | AnyPSE
  deriving (Eq, Ord, Show)

instance Null PrinSetExp where
  null = PowPSE null

makePrettySum ''PrinExp
makePrettySum ''PrinSetExp

data PrinDecl =
    SinglePD Prin
  | ArrayPD Prin ℕ
  deriving (Eq, Ord, Show)
makePrettySum ''PrinDecl

------------
--- Mode ---
------------



type Mode = AddTop (𝑃 PrinVal)

data ModeAny =
    Any
  | AddAny Mode
  deriving (Eq, Ord, Show)

instance Pretty ModeAny where
  pretty = \case
    Any → pretty "Any Mode"
    AddAny m → pretty m

----------------
-- Constraint --
----------------

-- C ∈ constraint ⩴  …
data Constr =
    SubsetC PrinSetExp PrinSetExp --  P ⊆ P  /  P c= P
  deriving (Eq, Ord, Show)
makePrettySum ''Constr

-----------------
-- Effect Mode --
-----------------

type EMode = AddTop PrinSetExp

------------
-- Effect --
------------

-- η ∈ effect ⩴  …
data Effect = Effect
  { effectInput  ∷ PrinSetExp
  , effectReveal ∷ PrinSetExp
  , effectMode   ∷ EMode
  } deriving (Eq, Ord, Show)
makePrettySum ''Effect
makeLenses ''Effect

----------
-- TVar --
----------

type TVar = 𝕏

----------
-- Prot --
----------

-- φ ∈ protocol ⩴  …
data Prot =
    PlainP -- plaintext
  | YaoNP  -- yao
  | Yao2P  -- yao2
  | BGWP   -- bgw
  | GMWP   -- gmw
  | BGVP   -- bgv
  | SPDZP  -- spdz
  | AutoP  -- auto
  deriving (Eq,Ord,Show)

instance Pretty Prot where
  pretty = \case
    PlainP → ppBdr "plainP"
    YaoNP → ppBdr "yaoNP"
    Yao2P → ppBdr "yao2P"
    BGWP → ppBdr "bgw"
    GMWP → ppBdr "gmw"
    BGVP → ppBdr "bgv"
    SPDZP → ppBdr "spdz"
    AutoP → ppBdr "auto"

-- Singleton for Prot
data SProt (p ∷ Prot) where
  SPlainP ∷ SProt 'PlainP
  SYaoNP  ∷ SProt 'YaoNP
  SYao2P  ∷ SProt 'Yao2P
  SBGWP   ∷ SProt 'BGWP
  SGMWP   ∷ SProt 'GMWP
  SBGVP   ∷ SProt 'BGVP
  SSPDZP  ∷ SProt 'SPDZP
  SAutoP  ∷ SProt 'AutoP

deriving instance Eq (SProt p)
deriving instance Ord (SProt p)
deriving instance Show (SProt p)

instance Pretty (SProt p) where
  pretty = \case
    SPlainP → ppLit "SPlainP"
    SYaoNP  → ppLit "SYaoNP"
    SYao2P  → ppLit "SYao2P"
    SBGWP   → ppLit "SBGWP"
    SGMWP   → ppLit "SGMWP"
    SBGVP   → ppLit "SBGVP"
    SSPDZP  → ppLit "SSPDZP"
    SAutoP  → ppLit "SAutoP"

instance DEqable SProt where
  deq sp₁ sp₂ = case (sp₁, sp₂) of
    (SPlainP, SPlainP) → YesDEq
    (SYaoNP , SYaoNP ) → YesDEq
    (SYao2P , SYao2P ) → YesDEq
    (SBGWP  , SBGWP  ) → YesDEq
    (SGMWP  , SGMWP  ) → YesDEq
    (SBGVP  , SBGVP  ) → YesDEq
    (SSPDZP , SSPDZP ) → YesDEq
    (SAutoP , SAutoP ) → YesDEq
    _ → NoDEq

instance DCmpable SProt where
  dcmp sp₁ sp₂ = case (sp₁, sp₂) of
    -- SPlain
    (SPlainP, SPlainP) → EQDCmp
    (SPlainP, _      ) → LTDCmp
    -- SYaoNP
    (SYaoNP , SPlainP) → GTDCmp
    (SYaoNP , SYaoNP ) → EQDCmp
    (SYaoNP , _      ) → LTDCmp
    -- SYao2P
    (SYao2P , SPlainP) → GTDCmp
    (SYao2P , SYaoNP ) → GTDCmp
    (SYao2P , SYao2P ) → EQDCmp
    (SYao2P , _      ) → LTDCmp
    -- SBGWP
    (SBGWP  , SPlainP) → GTDCmp
    (SBGWP  , SYaoNP ) → GTDCmp
    (SBGWP  , SYao2P ) → GTDCmp
    (SBGWP  , SBGWP  ) → EQDCmp
    (SBGWP  , _      ) → LTDCmp
    -- SGMWP
    (SGMWP  , SAutoP ) → LTDCmp
    (SGMWP  , SSPDZP ) → LTDCmp
    (SGMWP  , SBGVP  ) → LTDCmp
    (SGMWP  , SGMWP  ) → EQDCmp
    (SGMWP  , _      ) → GTDCmp
    -- SBGVP
    (SBGVP  , SAutoP ) → LTDCmp
    (SBGVP  , SSPDZP ) → LTDCmp
    (SBGVP  , SBGVP  ) → EQDCmp
    (SBGVP  , _      ) → GTDCmp
    -- SSPDZP
    (SSPDZP , SAutoP ) → LTDCmp
    (SSPDZP , SSPDZP ) → EQDCmp
    (SSPDZP , _      ) → GTDCmp
    -- SAutoP
    (SAutoP , SAutoP ) → EQDCmp
    (SAutoP , _      ) → GTDCmp

protFrSProt ∷ SProt p → Prot
protFrSProt = \case
  SPlainP → PlainP
  SYaoNP  → YaoNP
  SYao2P  → Yao2P
  SBGWP   → BGWP
  SGMWP   → GMWP
  SBGVP   → BGVP
  SSPDZP  → SPDZP
  SAutoP  → AutoP

---------------
-- Precision --
---------------

data IPrecision =
    InfIPr
  | FixedIPr ℕ ℕ -- whole number precision, and decimal precision
  deriving (Eq,Ord,Show)

iprDefault ∷ IPrecision
iprDefault = FixedIPr 32 0

instance Pretty IPrecision where
  pretty = \case
    InfIPr → concat
      [ ppPun "#"
      , ppBdr "∞"
      ]
    FixedIPr n₁ n₂
      | (n₁ ≡ 32) ⩓ (n₂ ≡ 0) → null
      | otherwise → concat
        [ ppPun "#"
        , pretty n₁
        , if n₂ ≡ 0
             then null
             else concat
               [ ppPun "."
               , pretty n₂
               ]
        ]

ppNatSymphony ∷ (Pretty a) ⇒ IPrecision → a → Doc
ppNatSymphony p n = concat [pretty n,ppLit "n",pretty p]

ppIntSymphony ∷ (Pretty a) ⇒ IPrecision → a → Doc
ppIntSymphony p i = concat [pretty i,pretty p]

data FPrecision =
    FixedFPr ℕ ℕ
  deriving (Eq,Ord,Show)

fprDefault ∷ FPrecision
fprDefault = FixedFPr 11 53

instance Pretty FPrecision where
  pretty = \case
    FixedFPr n₁ n₂
      | (n₁ ≡ 11) ⩓ (n₂ ≡ 53) → null
      | otherwise → concat
        [ ppPun "#"
        , pretty n₁
        , if n₂ ≡ 0
             then null
             else concat
               [ ppPun "."
               , pretty n₂
               ]
        ]

ppFltSymphony ∷ FPrecision → 𝔻 → Doc
ppFltSymphony p d = concat [pretty d,pretty p]

----------
-- Type --
----------

-- bτ ∈ base-type
data BaseType =
    UnitT                                       --  𝟙                          /  unit
  | 𝔹T                                          --  𝔹                          /  bool
  | ℕT IPrecision                               --  ℕ#n.n                      /  nat#n.n
  | ℤT IPrecision                               --  ℤ#n.n                      /  int#n.n
  | 𝔽T FPrecision                               --  𝔽#n                        /  float#n
  | 𝕊T                                          --  𝕊                          /  string
  | ℙT                                          --  ℙ                          /  prin
  | ℙsT                                         --  ℙs                         /  prins
  deriving (Eq,Ord,Show)
makePrettySum ''BaseType

-- τ ∈ type ⩴  …
data Type =
    VarT TVar                                   --  α                          /  α
  | BaseT BaseType
  | Type :+: Type                               --  τ + τ                      /  τ + τ
  | Type :×: Type                               --  τ × τ                      /  τ * τ

  | ListT Type                                --  list[n] τ                  /  list[n] τ
  | RefT (𝑂 EMode) Type                         --  ref{P} τ                   /  ref{P} τ
  | ArrT (𝑂 EMode) Type                       --  arr[P,n] τ                 /  arr[P,n] τ
  | (Type :→: (Effect ∧ Type)) 𝔹                    --  τ →{η} τ 𝔹                  /  τ ->{η} τ 𝔹
  | (𝕏 ∧ Type ∧ 𝐿 Constr) :→†: (Effect ∧ Type)  --  (x : τ | c,…,c) →{η} τ     /  (x : τ | c,…,c) ->{η} τ
  | ForallT TVar Type   --  ∀ α:κ,…,α:κ | c,…,c. τ     /  forall α:κ,…,α:κ | c,…,c. τ
  | SecT EMode Type                             --  τ{P}                       /  τ{P}
  | SSecT EMode Type                            --  τ{ssec:P}                  /  τ{ssec:P}
  | ISecT EMode Type                            --  τ{bundle:P}                /  τ{bundle:P}
  | ShareT Prot EMode Type                      --  τ{φ:P}                     /  τ{φ:P}
  | RecT TVar Type
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
    VarP Var            -- x        /  x
  | BulP                -- •        /  ()
  | EPrinSetP           -- {}       /  {}
  | NEPrinSetP 𝕏 Pat    -- {ρ}∪ψ    /  {ρ}\/ψ
  | ProdP Pat Pat       -- ψ,ψ      /  ψ,ψ
  | LP Pat              -- L ψ      /  L ψ
  | RP Pat              -- R ψ      /  R ψ
  | NilP                -- []       /  []
  | ConsP Pat Pat       -- ψ∷ψ      /  ψ::ψ
  | EBundleP            -- ⟪⟫       /  <<>>
  | NEBundleP 𝕏 Pat Pat -- ⟪ρ|ψ⟫⧺ψ  /  <<ρ|ψ>>++ψ
  | AscrP Pat Type      -- ψ : τ    /  ψ : τ
  | WildP               -- _        /  _
  -- [ψ₁;…;ψₙ] ≜ ψ₁ ∷ ⋯ ∷ ψₙ ∷ []
  -- ⟨ρ₁.ψ₁;…;ρₙ.ψₙ⟩ ≜ ⟨ρ₁.ψ₁⟩ ⧺ ⋯ ⧺ ⟨ρₙ.ψₙ⟩ ⧺ ⟨⟩
  deriving (Eq,Ord,Show)
makePrettySum ''Pat
makePrisms ''Pat

--------------------------
-- Primitive Operations --
--------------------------

data Op =
    OrO               -- e || e
  | AndO              -- e && e
  | NotO              -- not e
  | PlusO             -- e + e
  | MinusO            -- e - e
  | TimesO            -- e * e
  | ExpO              -- exp e
  | DivO              -- e / e
  | ModO              -- e % d
  | EqO               -- e == e
  | LTO               -- e < e
  | GTO               -- e > e
  | LTEO              -- e <= e
  | GTEO              -- e >= e
  | CondO             -- e ? e >< e
  | AbsO              -- abs_val e
  | SqrtO             -- sqrt e
  | LogO              -- log_base_2 e
  | NatO IPrecision   -- nat#n.n
  | IntO IPrecision   -- int#n.n
  | FltO FPrecision   -- flt#n.n
  | CeilO IPrecision  -- ceil#n.n
  | ToStringO         -- to_str e
  deriving (Eq,Ord,Show)
makePrettySum ''Op
makePrisms ''Op

-------------------
-- Program Terms --
-------------------

-- e ∈ term ⩴  …
type Exp = 𝐴 SrcCxt ExpR
data ExpR =
    VarE Var                                      -- x                       /  x
  | BulE                                          -- •                       /  ()
  | BoolE 𝔹                                       -- b                       /  b
  | NatE IPrecision ℕ                             -- n#n.n                   /  n#n.n
  | IntE IPrecision ℤ                             -- i#n.n                   /  i#n.n
  | FltE FPrecision 𝔻                             -- d#n                     /  d#n
  | StrE 𝕊                                        -- s                       /  s
  | PrinE PrinExp                                 -- ρe                      /  ρe
  | PrinSetE PrinSetExp                           -- ρse                     /  ρse
  | PrimE Op (𝐿 Exp)                              -- prim[⊙](e,…,e)          /  prim[⊙](e,…,e)

  | ProdE Exp Exp                                 -- e,e                     /  e,e
  | LE Exp                                        -- L e                     /  L e
  | RE Exp                                        -- R e                     /  R e
  | NilE                                          -- []                      /  []
  | ConsE Exp Exp                                 -- e∷e                     /  e::e
  | IfE Exp Exp Exp                               -- if e then e else e      /  if e then e else e
  | CaseE Exp (𝐿 (Pat ∧ Exp))                     -- case e {ψ→e;…;ψ→e}      /  case e {ψ->e;…;ψ->e}

  | LetE Pat Exp Exp                              -- let ψ = e in e          /  let ψ = e in e
  | LetTyE Pat Exp                                -- let ψ : τ in e          /  let ψ : τ in e
  | LamE (𝑂 Var) (𝐿 Pat) Exp                      -- λ [x] ψ…ψ → e           /  fun [x] ψ…ψ → e
  | TLamE TVar Exp                                -- Λ α → e                 /  abs α → e
  | AppE Exp Exp                                  -- e e                     /  e e
  | TAppE Exp Type                                -- e@τ                     /  e@τ

  | ReadE Type Exp                                -- read τ e                /  read τ e
  | WriteE Exp Exp                                -- write e e               /  write e e

  | TraceE Exp Exp                                -- trace e in e            /  trace e in e
  | AscrE Exp Type                                -- e:τ                     /  e:τ

  | RefE Exp                                      -- ref e                   /  ref e
  | RefReadE Exp                                  -- !e                      /  !e
  | RefWriteE Exp Exp                             -- e ≔ e                   /  e := e

  | ArrayE Exp Exp                                -- array[e] e              /  array[e] e
  | ArrayReadE Exp Exp                            -- e.e                     /  e.e
  | ArrayWriteE Exp Exp                           -- e ← e                   /  e <- e
  | ArraySizeE Exp                                -- size e                  /  size e

  | ParE PrinSetExp Exp                           -- par ρse e               /  par ρse e

  | RandE PrinSetExp BaseType                     -- rand ρse μ              /  rand ρse μ

  | ShareE Prot Type PrinSetExp PrinSetExp Exp    -- share{φ,τ:ρse→ρse} e    /  share{φ,τ:ρse->ρse} e
  | RevealE Prot Type PrinSetExp PrinSetExp Exp   -- reveal{φ,τ:ρse→ρse} e   /  reveal{φ,τ:ρse→ρse} e
  | SendE Type PrinSetExp PrinSetExp Exp          -- send{τ:ρse→ρse} e       /  send{τ:ρse->ρse} e

  | MuxIfE Exp Exp Exp                            -- mux if e then e else e  /  mux if e then e else e
  | MuxCaseE Exp (𝐿 (Pat ∧ Exp))                  -- mux case e {ψ→e;…;ψ→e}  /  mux case e {ψ->e;…;ψ->e}
  | ProcE Exp                                     -- proc e                  /  proc e
  | ReturnE Exp                                   -- return e                /  return e

  | BundleE (𝐿 (PrinExp ∧ Exp))                   -- ⟪e|e;…;e|e⟫             /  <<e|e;…;e|e>>
  | BundleAccessE Exp PrinExp                     -- e@e                     /  e@e
  | BundleUnionE Exp Exp                          -- e⧺e                     /  e++e

  | SeqE Exp Exp                                  -- e;e                     / e;e

  | DefaultE                                      -- _|_                     /  ⊥
  | FoldE Exp

  | UnfoldE  Exp

  deriving (Eq,Ord,Show)
  -- [e₁;…;eₙ] ≜ e₁ ∷ ⋯ ∷ eₙ ∷ []
makePrettySum ''ExpR

nullExp :: ExpR -> Exp
nullExp e = 𝐴 null e

buildLambda ∷ SrcCxt → Var → 𝐿 Pat → Exp → Exp
buildLambda c x ψs e
  | ψs ≡ Nil = e
  | otherwise = 𝐴 c $ LamE (Some x) ψs e

buildUnfixedLambda ∷ SrcCxt → Var → 𝐿 Pat → Exp → Exp
buildUnfixedLambda c x ψs e
  | ψs ≡ Nil = e
  | otherwise = 𝐴 c $ LamE None (VarP x :& ψs) e

---------------
-- Top-level --
---------------

-- tl ∈ top-level ⩴  …
type TL = 𝐴 SrcCxt TLR
data TLR =
    DeclTL 𝔹 Var Type               -- def [sec] x : τ            /  def [sec] x : τ
  | DefnTL 𝔹 Var (𝐿 Pat) Exp        -- def [sec] x ψ₁ … = e       /  def [sec] x  ψ₁ … = e
  | PrinTL (𝐿 PrinDecl)             -- principal ρ …              /  principal ρ …
  | ImportTL 𝕊                      -- import s                   /  import s
  deriving (Eq, Ord)
makePrettySum ''TLR
