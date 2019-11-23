module PSL.Parser where

import UVMHS
import AddToUVMHS

levelDO,levelIF,levelLAM,levelLET,levelCASE ∷ ℕ64
levelDO   = 𝕟64 10
levelIF   = 𝕟64 10
levelLAM  = 𝕟64 10
levelLET  = 𝕟64 10
levelCASE = 𝕟64 10

levelCOMMA,levelCONS,levelMPC,levelPAR,levelSHARE,levelASCR ∷ ℕ64

levelCOMMA   = 𝕟64 20
levelCONS    = 𝕟64 21
levelMPC     = 𝕟64 24
levelPAR     = 𝕟64 25
levelSHARE   = 𝕟64 25
levelASCR    = 𝕟64 29

levelCOND,levelCOMPARE,levelPLUS,levelTIMES,levelCIRCUIT,levelACCESS ∷ ℕ64
levelCOND    = 𝕟64 30
levelCOMPARE = 𝕟64 40
levelPLUS    = 𝕟64 50
levelTIMES   = 𝕟64 60
levelCIRCUIT = 𝕟64 70
levelACCESS  = 𝕟64 80

levelARROW,levelMPCTY,levelTUNION,levelTUPLE ∷ ℕ64
levelARROW  = 𝕟64 40
levelMPCTY  = 𝕟64 45
levelTUNION = 𝕟64 50
levelTUPLE  = 𝕟64 60

levelAPP ∷ ℕ64
levelAPP = 𝕟64 100

levelMODE,levelINDEX ∷ ℕ64
levelMODE  = 𝕟64 200
levelINDEX = 𝕟64 200

lexer ∷ Lexer CharClass ℂ TokenClassBasic ℕ64 TokenBasic
lexer = lexerBasic puns kws prim ops
  where
    puns = list 
      [ "(",")","{","}","[","]","<",">","⟨","⟩"
      , ".",",",":",";"
      , "→","->"
      , "⇒","=>"
      , "←","<-"
      , "↣",">->"
      , "⪫","->-"
      , "⫫","_||_"
      , "="
      , "~"
      , "_"
      , "⌊","|_"
      , "⌋","_|"
      , "⌈","|^"
      , "⌉","^|"
      ]
    kws = list
      [ "primitive"
      , "principal"
      , "trust"
      , "security"
      , "wbfold"
      , "from"
      , "def"
      , "λ","fun"
      , "rλ","rfun"
      , "Λ","abs"
      , "∀","forall"
      , "let","in"
      , "if","then","else"
      , "circuit"
      , "mpc"
      , "reveal"
      , "do"
      , "case"
      , "share"
      ]
    prim = list
      [ "yao","bgw","gmw","none"
      , "nshare","yshare","gshare","sshare"
      , "ssec","isec"
      , "☆","type"
      , "ℙ","prin"
      , "ℤ","int"
      , "ℤ64","int64"
      , "ℕ","nat"
      , "ℕ64","nat64"
      , "𝔹","bool"
      , "𝕊","string"
      , "MPC"
      , "CIR"
      , "list"
      , "true","false"
      , "𝟙","unit"
      , "•","()"
      , "𝟘","empty"
      , "[]"
      , "∷","::"
      , "ncir","bcir","acir","ccir","ucir"
      ]
    ops = list 
      [ "+","-"
      , "×","*"
      , "/"
      , "≡","=="
      , "≤","<="
      , "<"
      , "^"
      , "?"
      , "◇"
      , "⊆"
      , "@"
      ]

testLexer ∷ IO ()
testLexer = rtimeIO "" $ do
  s₁ ← read "files/pantheon/lib.psl"
  tokenizeIOMain lexer $ tokens s₁
  s₂ ← read "files/pantheon/euclid.psl"
  tokenizeIOMain lexer $ tokens s₂
  s₃ ← read "files/pantheon/simple.psl"
  tokenizeIOMain lexer $ tokens s₃
  return ()

----------
-- Kind --
----------

-- κ ∈ kind ⩴ ☆ | ℙ
type AKind = Annotated FullContext Kind
data Kind =
    TypeK  -- ☆  /  type
  | PrinK  -- ℙ  /  prin
  deriving (Eq,Ord,Show)
makePrettySum ''Kind

pKind ∷ CParser TokenBasic AKind
pKind = cpWithContextRendered $ concat
  [ do concat [cpSyntax "☆",cpSyntax "type"] ; return TypeK
  , do concat [cpSyntax "ℙ",cpSyntax "prin"] ; return PrinK
  ]

----------
-- Prin --
----------

-- ρ ∈ prin ≜ 𝕏
type APrin = Annotated FullContext Prin
type Prin = 𝕏

pPrin ∷ CParser TokenBasic APrin
pPrin = cpWithContextRendered cpName

--------------
-- Prin-set --
--------------

-- P ∈ prin-set ≜ ℘(Prin)
type APrins = Annotated FullContext Prins
type Prins = 𝑃 APrin -- ρ,…,ρ

pPrins ∷ CParser TokenBasic APrins
pPrins = cpWithContextRendered $ pow ^$ cpManySepBy (cpSyntax ",") pPrin

------------
-- Scheme --
------------

-- σ ∈ scheme ⩴  add | shamir
type AScheme = Annotated FullContext Scheme
data Scheme = 
    NoS      -- nshare
  | GMWS     -- gshare
  | YaoS     -- yshare
  | ShamirS  -- sshare
  deriving (Eq,Ord,Show)
makePrettySum ''Scheme

pScheme ∷ CParser TokenBasic AScheme
pScheme = cpWithContextRendered $ concat
  [ do cpSyntax "nshare" ; return NoS
  , do cpSyntax "gshare" ; return GMWS
  , do cpSyntax "yshare" ; return YaoS
  , do cpSyntax "sshare" ; return ShamirS
  ]

-----------------
-- Circuit Ops --
-----------------

-- ς ∈ circuit-ops ⩴ bcir | acir
type ACirOps = Annotated FullContext CirOps
data CirOps = 
    NoCO     -- ncir
  | BoolCO   -- bcir
  | ArithCO  -- acir
  | CompCO   -- ccir
  | UnivCO   -- ucir
  deriving (Eq,Ord,Show)
makePrettySum ''CirOps

pCirOps ∷ CParser TokenBasic ACirOps
pCirOps = cpWithContextRendered $ concat
  [ do cpSyntax "ncir" ; return NoCO
  , do cpSyntax "bcir" ; return BoolCO
  , do cpSyntax "acir" ; return ArithCO
  , do cpSyntax "ccir" ; return CompCO
  , do cpSyntax "ucir" ; return UnivCO
  ]

----------------
-- Constraint --
----------------

type AConstr = Annotated FullContext Constr
data Constr =
    SubsetC APrins APrins
  deriving (Eq,Ord,Show)
makePrettySum ''Constr

pConstr ∷ CParser TokenBasic AConstr
pConstr = cpWithContextRendered $ concat
  [ do cpSyntax "{"
       ps₁ ← pPrins
       cpSyntax "}"
       concat [cpSyntax "⊆",cpSyntax "<="]
       cpSyntax "{"
       ps₂ ← pPrins
       cpSyntax "}"
       return $ SubsetC ps₁ ps₂
  ]

----------
-- Type --
----------

-- τ ∈ type ⩴ α | 𝟙 | 𝔹 | 𝕊 
--          | ℕn.n | ℤn.n | 𝔽n
--          | τ + τ | τ × τ | list τ | array τ
--          | τ → τ 
--          | ∀ α:κ. [c,…,c] ⇒ τ
--          | τ{ssec:P} 
--          | τ{isec:P} 
--          | τ{ς:σ:P} 
--          | MPC{P} τ
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

pType ∷ CParser TokenBasic AType
pType = fmixfixWithContext "type" $ concat
  [ fmixTerminal $ concat
      [ do x ← cpName ; return $ VarT x
      , do concat [cpSyntax "𝟙",cpSyntax "unit"] ; return UnitT
      , do concat [cpSyntax "𝔹",cpSyntax "bool"] ; return 𝔹T
      , do concat [cpSyntax "𝕊",cpSyntax "string"] ; return 𝕊T
      , do concat [cpSyntax "ℕ",cpSyntax "nat"]
           return $ ℕT None
      , do concat [cpSyntax "ℕ64",cpSyntax "nat64"]
           n ← cpOptional $ do
             cpSyntax "."
             cpNatural
           return $ ℕT $ Some $ 64 :* n
      , do concat [cpSyntax "ℤ",cpSyntax "int"]
           return $ ℤT None
      , do concat [cpSyntax "ℤ64",cpSyntax "int64"]
           n ← cpOptional $ do
             cpSyntax "."
             cpNatural
           return $ ℤT $ Some $ 64 :* n
      , do concat [cpSyntax "𝔽64",cpSyntax "float64"]
           return $ 𝔽T 64
      , do cpSyntax "(" ; τ ← pType ; cpSyntax ")" ; return $ extract τ
      ]
  , fmixInfixL levelPLUS $ do concat [cpSyntax "+"] ; return (:+:)
  , fmixInfixL levelTIMES $ do concat [cpSyntax "×",cpSyntax "*"] ; return (:×:)
  , fmixPrefix levelAPP $ do cpSyntax "list" ; return ListT
  , fmixInfixR levelARROW $ do concat [cpSyntax "→",cpSyntax "->"] ; return (:→:)
  , fmixPrefix levelLAM $ do
      concat [cpSyntax "∀", cpSyntax "forall"]
      α ← cpName
      cpSyntax ":"
      κ ← pKind
      cpSyntax "."
      cs ← ifNone Nil ^$ cpOptional $ do
        cs ← cpManySepBy (cpSyntax ",") pConstr
        concat [cpSyntax "⇒",cpSyntax "=>"]
        return cs
      return $ ForallT α κ cs
  , fmixPostfix levelMODE $ do 
      cpSyntax "{"
      cpSyntax "ssec"
      cpSyntax ":"
      ps ← pPrins
      cpSyntax "}"
      return $ \ τ → SSecT τ ps
  , fmixPostfix levelMODE $ do 
      cpSyntax "{"
      cpSyntax "isec"
      cpSyntax ":"
      ps ← pPrins
      cpSyntax "}"
      return $ \ τ → ISecT τ ps
  , fmixPostfix levelMODE $ do 
      cpSyntax "{"
      ς :* σ ← tries
        [ do ς ← pCirOps
             Annotated cxt () ← cpWithContextRendered $ cpSyntax ":"
             σ ← ifNone (Annotated cxt NoS) ^$ cpOptional $ do
                 σ ← pScheme
                 cpSyntax ":"
                 return σ
             return $ ς :* σ
        , do σ ← pScheme
             Annotated cxt () ← cpWithContextRendered $ cpSyntax ":"
             return $ Annotated cxt NoCO :* σ
        ]
      ps ← pPrins
      cpSyntax "}"
      return $ \ τ → CirT τ ς σ ps
  , fmixPrefix levelMPCTY $ do
      cpSyntax "MPC"
      cpSyntax "{"
      ps ← pPrins
      -- concat [cpSyntax "⪫",cpSyntax ">>-"]
      -- ps₂ ← pPrins
      cpSyntax "}"
      return $ MpcT ps
  ]

--------------
-- Literals --
--------------

pBool ∷ CParser TokenBasic 𝔹
pBool = concat
  [ do cpSyntax "true" ; return True
  , do cpSyntax "false" ; return False
  ]

----------
-- Prot --
----------

-- φ ∈ protocol ⩴ yao | bgw | gmw
type AProt = Annotated FullContext Prot
data Prot = 
    YaoP  -- yao
  | BGWP  -- bgw
  | GMWP  -- gmw
  | NoneP -- none
  deriving (Eq,Ord,Show)
makePrettySum ''Prot

pProt ∷ CParser TokenBasic AProt
pProt = cpWithContextRendered $ concat
  [ do cpSyntax "yao" ; return YaoP
  , do cpSyntax "bgw" ; return BGWP
  , do cpSyntax "gmw" ; return GMWP
  , do cpSyntax "none" ; return NoneP
  ]

-------------
-- Pattern --
-------------

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

pPat ∷ CParser TokenBasic APat
pPat = fmixfixWithContext "pattern" $ concat
  [ fmixTerminal $ concat
      [ do x ← cpName ; return $ VarP x
      , do concat [cpSyntax "•",cpSyntax "()"] ; return BulP
      , do cpSyntax "[]" ; return NilP
      , do concat [cpSyntax "∅",cpSyntax "empty"] ; return EmptyP
      , do cpSyntax "_" ; return WildP
      , do cpSyntax "(" ; ψ ← pPat ; cpSyntax ")" ; return $ extract ψ
      , do cpSyntax "["
           ψs ← cpManySepByContext cpWithContextRendered (cpSyntax ";") pPat
           a ← annotatedTag ^$ cpWithContextRendered $ cpSyntax "]"
           return $ extract $ foldrOnFrom ψs (Annotated a NilP) $ \ (Annotated a₁ ψ₁) ψ₂ → Annotated a₁ $ ConsP ψ₁ ψ₂
      , do concat [cpSyntax "⟨",cpSyntax "<"]
           ψρs ← cpManySepByContext cpWithContextRendered (cpSyntax ";") $ do
             ψ ← pPat
             cpSyntax "@"
             ρ ← pPrin
             return $ ψ :* ρ
           a ← annotatedTag ^$ cpWithContextRendered $ concat [cpSyntax "⟩",cpSyntax ">"]
           return $ extract $ foldOnFrom ψρs (Annotated a EmptyP) $ \ (Annotated a₁ (ψ₁ :* ρ₁)) ψ₂ → Annotated a₁ $ BundleP ψ₁ ρ₁ ψ₂
      ]
  , fmixPrefix levelAPP $ do concat [cpSyntax "ι₁",cpSyntax "in1"] ; return Inj1P
  , fmixPrefix levelAPP $ do concat [cpSyntax "ι₂",cpSyntax "in2"] ; return Inj2P
  , fmixInfixL levelCOMMA $ do cpSyntax "," ; return TupP
  , fmixInfixR levelPLUS $ do concat [cpSyntax "∷",cpSyntax "::"] ; return ConsP
  , fmixPrefix levelCONS $ do
      concat [cpSyntax "⟨",cpSyntax "<"]
      ψ ← pPat
      cpSyntax "@"
      ρ ← pPrin
      concat [cpSyntax "⟩",cpSyntax ">"]
      concat [cpSyntax "⧺",cpSyntax "++"]
      return $ BundleP ψ ρ
  ]

-------------------
-- Program Terms --
-------------------

-- e ∈ term ⩴ x | b | s | i | d | •
--          | if e then e else e
--          | ιₙ | e,e | [] | e∷e
--          | let ψ = e in e
--          | case e {ψ→e;…;ψ→e}
--          | λ x ψ → e
--          | e e
--          | Λ α → e
--          | e@τ
--          | par{P} e
--          | ~e
--          | share{σ:P} e
--          | ∅ | ⟨P⇒e⟩ | e~e
--          | mpc{φ:P} e
--          | return e
--          | x ← e ; e
--          | prim[⊙](e,…,e)
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
  | HoleE                          -- _                     /  _
  deriving (Eq,Ord,Show)
  -- [e₁;…;eₙ] ≜ e₁ ∷ ⋯ ∷ eₙ ∷ []
  -- ⟨e₁@ρ₁;…;eₙ@ρₙ⟩ ≜ ⟨e₁@ρ₁⟩ ⧺ ⋯ ⧺ ⟨eₙ@ρₙ⟩
makePrettySum ''Exp

pExp ∷ CParser TokenBasic AExp
pExp = fmixfixWithContext "exp" $ concat
  [ fmixTerminal $ concat
      [ do x ← cpName ; return $ VarE x
      , do b ← pBool ; return $ BoolE b
      , do s ← cpString ; return $ StrE s
      , do i ← cpInteger ; return $ IntE i
      , do d ← cpDouble ; return $ DblE d
      , do concat [cpSyntax "•",cpSyntax "()"] ; return BulE
      , do cpSyntax "[]" ; return NilE
      , do cpSyntax "case"
           e ← pExp
           cpSyntax "{"
           φes ← cpManySepBy (cpSyntax ";") $ do 
             φ ← pPat
             concat [cpSyntax "→",cpSyntax "->"]
             e' ← pExp
             return $ φ :* e'
           cpSyntax "}"
           return $ CaseE e φes
      , do concat [cpSyntax "∅",cpSyntax "empty"] ; return EmptyE
      , do concat [cpSyntax "⟨",cpSyntax "<"] 
           e ← pExp
           cpSyntax "@"
           ρ ← pPrin
           concat [cpSyntax "⟩",cpSyntax ">"]
           return $ BundleOneE e ρ
      , do cpSyntax "_" ; return HoleE
      , do cpSyntax "(" ; e ← pExp ; cpSyntax ")" ; return $ extract e
      , do cpSyntax "["
           es ← cpManySepByContext cpWithContextRendered (cpSyntax ";") pExp
           a ← annotatedTag ^$ cpWithContextRendered $ cpSyntax "]"
           return $ extract $ foldrOnFrom es (Annotated a NilE) $ \ (Annotated a₁ e₁) e₂ → Annotated a₁ $ ConsE e₁ e₂
      , do concat [cpSyntax "⟨",cpSyntax "<"]
           eρs ← cpManySepByContext cpWithContextRendered (cpSyntax ";") $ do
             e ← pExp
             cpSyntax "@"
             ρ ← pPrin
             return $ e :* ρ
           a ← annotatedTag ^$ cpWithContextRendered $ concat [cpSyntax "⟩",cpSyntax ">"]
           return $ extract $ foldOnFrom eρs (Annotated a EmptyE) $ \ (Annotated a₁ (e₁ :* ρ₁)) e₂ → 
             Annotated a₁ $ BundleUnionE (Annotated a₁ $ BundleOneE e₁ ρ₁) e₂
      , do cpSyntax "⟨"
           pes ← cpManySepBy (cpSyntax ";") $ do
             p ← pPrin
             concat [cpSyntax "⇒",cpSyntax "=>"]
             e ← pExp
             return $ p :* e
           cpSyntax "⟩"
           return $ BundleSetE pes
      ]
  , fmixPrefix levelIF $ do
      cpSyntax "if"
      e₁ ← pExp
      cpSyntax "then"
      e₂ ← pExp
      cpSyntax "else"
      return $ IfE e₁ e₂
  , fmixPrefix levelAPP $ do concat [cpSyntax "ι₁",cpSyntax "in1"] ; return Inj1E
  , fmixPrefix levelAPP $ do concat [cpSyntax "ι₂",cpSyntax "in2"] ; return Inj2E
  , fmixInfixL levelCOMMA $ do cpSyntax "," ; return TupE
  , fmixInfixR levelCONS $ do concat [cpSyntax "∷",cpSyntax "::"] ; return ConsE
  , fmixPrefix levelLET $ do
      cpSyntax "let"
      x ← cpName
      cpSyntax ":"
      τ ← pType
      void $ cpOptional $ cpSyntax "in"
      return $ LetTyE x τ
  , fmixPrefix levelLET $ do
      cpSyntax "let"
      ψ ← pPat
      cpSyntax "="
      e ← pExp
      void $ cpOptional $ cpSyntax "in"
      return $ LetE ψ e
  , fmixPrefix levelLAM $ do
      concat [cpSyntax "λ",cpSyntax "fun"]
      ψ ← pPat
      concat [cpSyntax "→",cpSyntax "->"]
      return $ LamE None ψ
  , fmixPrefix levelLAM $ do
      concat [cpSyntax "rλ",cpSyntax "rfun"]
      x ← cpName
      ψ ← pPat
      concat [cpSyntax "→",cpSyntax "->"]
      return $ LamE (Some x) ψ
  , fmixInfixL levelAPP $ return AppE
  , fmixPrefix levelLAM $ do
      concat [cpSyntax "Λ",cpSyntax "abs"]
      α ← cpName
      concat [cpSyntax "→",cpSyntax "->"]
      return $ TLamE α
  , fmixPostfix levelAPP $ do
      cpSyntax "@"
      τ ← pType
      return $ \ e → TAppE e τ
  , fmixPrefix levelPAR $ do
      cpSyntax "{"
      p ← pPrin
      cpSyntax "}"
      return $ SoloE p
  , fmixPrefix levelPAR $ do 
      cpSyntax "par"
      cpSyntax "{"
      ps ← pPrins
      cpSyntax "}"
      return $ ParE ps
  , fmixPrefix levelCIRCUIT $ do cpSyntax "~" ; return CirE
  , fmixPrefix levelSHARE $ do 
      cpSyntax "share"
      cpSyntax "{"
      σO ← cpOptional $ do
        σ ← pScheme
        cpSyntax ":"
        return σ
      ps ← pPrins
      cpSyntax "}"
      return $ ShareE σO ps
  , fmixPostfix levelACCESS $ do cpSyntax "." ; p ← pPrin ; return $ \ e → BundleAccessE e p
  , fmixInfixL levelPLUS $ do concat [cpSyntax "⧺",cpSyntax "++"] ; return BundleUnionE
  , fmixPrefix levelMPC $ do
      cpSyntax "mpc"
      cpSyntax "{"
      φ ← pProt
      cpSyntax ":"
      ps ← pPrins
      cpSyntax "}"
      return $ MPCE φ ps
  , fmixPrefix levelMPC $ do
      cpSyntax "reveal"
      cpSyntax "{"
      ps ← pPrins
      cpSyntax "}"
      return $ RevealE ps
  , fmixPrefix levelAPP $ do cpSyntax "return" ; return ReturnE
  , fmixPrefix levelDO $ do
      cpSyntax "let"
      ψ ← pPat
      concat [cpSyntax "←",cpSyntax "<-"]
      e ← pExp
      void $ cpOptional $ cpSyntax "in"
      return $ BindE ψ e
  , fmixPostfix levelASCR $ do
      cpSyntax ":"
      τ ← pType
      return $ \ e → AscrE e τ
  , fmixInfixL levelPLUS $ do concat [cpSyntax "∨",cpSyntax "||"] ; return $ \ e₁ e₂ → PrimE "OR" $ list [e₁,e₂]
  , fmixInfixL levelTIMES $ do concat [cpSyntax "∧",cpSyntax "&&"] ; return $ \ e₁ e₂ → PrimE "AND" $ list [e₁,e₂]
  , fmixInfixL levelPLUS $ do cpSyntax "+" ; return $ \ e₁ e₂ → PrimE "PLUS" $ list [e₁,e₂]
  , fmixInfixL levelTIMES $ do cpSyntax "×" ; return $ \ e₁ e₂ → PrimE "TIMES" $ list [e₁,e₂]
  , fmixInfixL levelTIMES $ do cpSyntax "/" ; return $ \ e₁ e₂ → PrimE "DIVIDE" $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do cpSyntax "<" ; return $ \ e₁ e₂ → PrimE "LT" $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do concat [cpSyntax "≤",cpSyntax "<="] ; return $ \ e₁ e₂ → PrimE "LTE" $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do concat [cpSyntax "≡",cpSyntax "=="] ; return $ \ e₁ e₂ → PrimE "EQ" $ list [e₁,e₂]
  , fmixInfixR levelCOND $ do
      cpSyntax "?"
      e₂ ← pExp
      cpSyntax "◇"
      return $ \ e₁ e₃ → PrimE "COND" $ list [e₁,e₂,e₃]
    
  ]
      
-- s ∈ top-level ⩴ def x : τ | def x = τ
--               | principal ρ
--               | trust P
--               | security P ⫫ P
--               | primitive x : τ
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

pTL ∷ CParser TokenBasic ATL
pTL = cpWithContextRendered $ concat
  [ do cpSyntax "def"
       x ← cpName
       concat
         [ do cpSyntax ":"
              τ ← pType
              return $ DeclTL x τ
         , do cpSyntax "="
              e ← pExp
              return $ DefnTL x e
         ]
  , do cpSyntax "principal"
       ρ ← pPrin
       return $ PrinTL ρ
  , do cpSyntax "trust"
       ps ← pPrins
       return $ TrustTL ps
  , do cpSyntax "security"
       ps₁ ← pPrins
       concat [cpSyntax "⫫",cpSyntax "_||_"]
       ps₂ ← pPrins
       return $ SecurityTL ps₁ ps₂
  , do cpSyntax "primitive"
       x ← cpName
       cpSyntax ":"
       τ ← pType
       return $ PrimTL x τ
  ]

cpTLs ∷ CParser TokenBasic (𝐿 ATL)
cpTLs = cpMany pTL

testExample ∷ 𝕊 → IO ()
testExample fn = do
  s ← read $ "examples/" ⧺ fn ⧺ ".psl"
  let ts = tokens s
  ls ← tokenizeIO lexer ts
  _tls ← parseIO cpTLs ls
  out $ "DONE: " ⧺ fn

testParser ∷ IO ()
testParser = do
  testExample "e1"
  -- s₁ ← read "examples/lib.psl"
  -- let ts₁ = tokens s₁
  -- ls₁ ← tokenizeIO lexer ts₁
  -- _tls₁ ← parseIO cpTLs ls₁
  -- out "lib done"
  -- s₂ ← read "examples/simple.psl"
  -- let ts₂ = tokens s₂
  -- ls₂ ← tokenizeIO lexer ts₂
  -- _tls₂ ← parseIO cpTLs ls₂
  -- out "simple done"
  -- s₃ ← read "examples/isort.psl"
  -- let ts₃ = tokens s₃
  -- ls₃ ← tokenizeIO lexer ts₃
  -- _tls₃ ← parseIO cpTLs ls₃
  -- out "isort done"
  -- s₄ ← read "examples/msort.psl"
  -- let ts₄ = tokens s₄
  -- ls₄ ← tokenizeIO lexer ts₄
  -- _tls₄ ← parseIO cpTLs ls₄
  -- out "msort done"
  -- s₅ ← read "examples/euclid.psl"
  -- let ts₅ = tokens s₅
  -- ls₅ ← tokenizeIO lexer ts₅
  -- _tls₅ ← parseIO cpTLs ls₅
  -- out "euclid done"
