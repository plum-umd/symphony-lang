module PSL.Parser where

import UVMHS

lexer ∷ Lexer CharClass ℂ TokenClassBasic ℕ64 TokenBasic
lexer = lexerBasic puns kws prim ops
  where
    puns = list 
      [ "(",")","{","}","[","]","<",">","⟨","⟩"
      , ",",":",";"
      , "→","->"
      , "←","<-"
      , "↣",">->"
      , "⪫","->-"
      , "⫫","_||_"
      , "="
      , "~"
      , "_"
      ]
    kws = list
      [ "primitive"
      , "principal"
      , "trust"
      , "security"
      , "def"
      , "λ","fun"
      , "Λ","abs"
      , "let","in"
      , "if","then","else"
      , "circuit"
      , "mpc"
      , "do"
      , "case"
      ]
    prim = list
      [ "yao","bgw","gmw","none"
      , "☆","type"
      , "ℙ","prin"
      , "ℤ","int"
      , "𝔹","bool"
      , "MPC"
      , "CIR"
      , "list"
      , "true","false"
      , "𝟙","unit"
      , "•","()"
      , "𝟘","empty"
      , "∷","::"
      ]
    ops = list 
      [ "+","-"
      , "×","*"
      , "/"
      , "≡","=="
      , "≤","<="
      , "<"
      , "^"
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
-- Prin --
----------

-- ρ ∈ prin ≜ 𝕏
type APrin = Annotated FullContext Prin
type Prin = 𝕏

pPrin ∷ CParser TokenBasic APrin
pPrin = cpWithContextRendered cpName

----------
-- Prin --
----------

-- P ∈ prin-set ≜ ℘(Prin)
type APrins = Annotated FullContext Prins
type Prins = 𝑃 APrin -- ρ,…,ρ

pPrins ∷ CParser TokenBasic APrins
pPrins = cpWithContextRendered $ pow ^$ cpManySepBy (cpSyntax ",") pPrin

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

-- -----------
-- -- Share --
-- -----------
-- 
-- -- σ ∈ share ⩴ ρ | φ:P
-- type AShare = Annotated FullContext Share
-- data Share = 
--     SoloS APrin         -- ρ
--   | ManyS AProt APrins  -- φ:P
--   deriving (Eq,Ord,Show)
-- makePrettySum ''Share
-- 
-- pShare ∷ CParser TokenBasic AShare
-- pShare = cpWithContextRendered $ concat
--   [ SoloS ^$ pPrin
--   , do φ ← pProt ; cpSyntax ":" ; ps ← pPrins ; return $ ManyS φ ps
--   ]

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

-------------
-- CirType --
-------------

-- cbτ ∈ circuit-base-type ⩴ ℤ | 𝔹
type ACirBaseType = Annotated FullContext CirBaseType
data CirBaseType =
    ℤCBT                            -- ℤ          /  int
  | 𝔹CBT                            -- 𝔹          /  bool
  | ACirBaseType :×♯: ACirBaseType  -- cbτ × cbτ  /  cbτ * cbτ
  deriving (Eq,Ord,Show)
makePrettySum ''CirBaseType

pCirBaseType ∷ CParser TokenBasic ACirBaseType
pCirBaseType = fmixfixWithContext "circuit-base-type" $ concat
  [ fmixTerminal $ concat
      [ do concat [cpSyntax "ℤ",cpSyntax "int"] ; return ℤCBT
      , do concat [cpSyntax "𝔹",cpSyntax "bool"] ; return 𝔹CBT
      ]
  , fmixInfixL (𝕟64 60) $ do concat [cpSyntax "×",cpSyntax "*"] ; return (:×♯:)
  ]

-- cτ ∈ circuit-type ⩴ cbτ
--                   | cbτ ↣ cbτ
type ACirType = Annotated FullContext CirType
data CirType =
    BaseCT ACirBaseType            -- cbτ        /  cbτ
  | ACirBaseType :↣: ACirBaseType  -- cbτ ↣ cbτ  /  cbτ >-> cbτ
  deriving (Eq,Ord,Show)
makePrettySum ''CirType

pCirType ∷ CParser TokenBasic ACirType
pCirType = cpWithContextRendered $ do
  bτ₁ ← pCirBaseType
  concat
    [ do concat [cpSyntax "↣",cpSyntax ">->"]
         bτ₂ ← pCirBaseType
         return $ bτ₁ :↣: bτ₂
    , return $ BaseCT bτ₁
    ]

-- ς ∈ circuit-ops
type ACirOps = Annotated FullContext CirOps
data CirOps = 
    BoolCO   -- bool
  | ArithCO  -- arith
  deriving (Eq,Ord,Show)
makePrettySum ''CirOps

pCirOps ∷ CParser TokenBasic ACirOps
pCirOps = cpWithContextRendered $ concat
  [ do cpSyntax "bool" ; return BoolCO
  , do cpSyntax "arith" ; return ArithCO
  ]

----------
-- Type --
----------

-- τ ∈ type ⩴ α | 𝟙 | ℤ | 𝔹
--          | τ × τ | τ → τ 
--          | τ{P} | τ[φ:P] | τ⟨P⟩ 
--          | CIR{ς:P} cτ | MPC{P ⪫ P} τ
--          | list τ
type AType = Annotated FullContext Type
data Type =
    VarT 𝕏                        -- α             /  α
  | UnitT                         -- 𝟙             /  unit
  | ℤT                            -- ℤ             /  int
  | 𝔹T                            -- 𝔹             /  bool
  | AType :×: AType               -- τ × τ         /  τ * τ̃
  | AType :→: AType               -- τ → τ         /  τ -> τ
  | LocT AType APrins             -- τ{P}          /  τ{P}
  | ShareT AType AProt APrins     -- τ[φ:P]        /  τ[φ:P]
  | BundleT AType APrins          -- τ⟨P⟩          /  τ<P>
  | CirT ACirOps APrins ACirType  -- CIR{ς:P} cτ   /  CIR cτ
  | MpcT APrins APrins AType      -- MPC{P ⪫ P} τ  /  MPC{P >- P} τ
  | ListT AType                   -- list τ        /  list τ
  deriving (Eq,Ord,Show)
makePrettySum ''Type

pType ∷ CParser TokenBasic AType
pType = fmixfixWithContext "type" $ concat
  [ fmixTerminal $ concat
      [ do x ← cpName ; return $ VarT x
      , do concat [cpSyntax "𝟙",cpSyntax "unit"] ; return UnitT
      , do concat [cpSyntax "ℤ",cpSyntax "int"] ; return ℤT
      , do concat [cpSyntax "𝔹",cpSyntax "bool"] ; return 𝔹T
      , do cpSyntax "CIR" 
           cpSyntax "{"
           ς ← pCirOps
           cpSyntax ":"
           ps ← pPrins
           cpSyntax "}"
           cτ ← pCirType 
           return $ CirT ς ps cτ
      ]
  , fmixInfixL (𝕟64 60) $ do concat [cpSyntax "×",cpSyntax "*"] ; return (:×:)
  , fmixInfixR (𝕟64 40) $ do concat [cpSyntax "→",cpSyntax "->"] ; return (:→:)
  , fmixPostfix (𝕟64 100) $ do 
      cpSyntax "{"
      ps ← pPrins
      cpSyntax "}"
      return $ \ τ → LocT τ ps
  , fmixPostfix (𝕟64 100) $ do 
      cpSyntax "["
      φ ← pProt
      cpSyntax ":"
      ps ← pPrins
      cpSyntax "]"
      return $ \ τ → ShareT τ φ ps
  , fmixPostfix (𝕟64 100) $ do 
      cpSyntax "⟨"
      ps ← pPrins
      cpSyntax "⟩"
      return $ \ τ → BundleT τ ps
  , fmixPrefix (𝕟64 200) $ do
      cpSyntax "MPC"
      cpSyntax "{"
      ps₁ ← pPrins
      concat [cpSyntax "⪫",cpSyntax ">>-"]
      ps₂ ← pPrins
      cpSyntax "}"
      return $ MpcT ps₁ ps₂
  , fmixPrefix (𝕟64 200) $ do cpSyntax "list" ; return ListT
  ]

--------------
-- Literals --
--------------

pBool ∷ CParser TokenBasic 𝔹
pBool = concat
  [ do cpSyntax "true" ; return True
  , do cpSyntax "false" ; return False
  ]

---------------------
-- Circuit Pattern --
---------------------

-- cψ ∈ pattern ⩴ x | cψ,cψ | _
type ACirPat = Annotated FullContext CirPat
data CirPat =
    VarCirP 𝕏                -- x      /  x
  | TupCirP ACirPat ACirPat  -- cψ,cψ  /  cψ,cψ
  | WildCirP                 -- _      /  _
  deriving (Eq,Ord,Show)
makePrettySum ''CirPat

pCirPat ∷ CParser TokenBasic ACirPat
pCirPat = fmixfixWithContext "circuit-pattern" $ concat
  [ fmixTerminal $ concat
      [ do x ← cpName ; return $ VarCirP x
      , do cpSyntax "_" ; return WildCirP
      ]
  , fmixInfixL (𝕟64 20) $ do cpSyntax "," ; return TupCirP
  ]

-------------------
-- Circuit Terms --
-------------------

-- ce ∈ circuit-term ⩴ i | b | ν | x | ~x | ⌊e⌋
--                   | let ν,…,ν = ce in ce
--                   | λ ν,…,ν → ce
--                   | ce(ce,…,ce)
type ACirExp = Annotated FullContext CirExp
data CirExp =
    IntC ℤ                         -- i                  /  i
  | BoolC 𝔹                        -- b                  /  b
  | VarC 𝕏                         -- x                  /  x
  | EmbedC AExp                    -- ⌊e⌋                /  |_e_|
  | LetC ACirPat ACirExp ACirExp   -- let cψ = ce in ce  /  let cψ = ce in ce
  | LamC ACirPat ACirExp           -- λ cψ → ce          /  fun cψ -> ce
  | AppC ACirExp ACirExp           -- ce ce              /  ce ce
  | ShareC ACirExp AProt APrins    -- ce[φ:P]            /  ce[φ:P]
  | PrimC 𝕊 (𝐿 ACirExp)            -- φₓ[ce,…,ce]        /  φₓ[ce,…,ce]
  deriving (Eq,Ord,Show)

pCirExp ∷ CParser TokenBasic ACirExp
pCirExp = fmixfixWithContext "circuit" $ concat
  [ fmixTerminal $ concat
      [ do i ← cpInteger ; return $ IntC i
      , do b ← pBool ; return $ BoolC b
      , do x ← cpName ; return $ VarC x
      , do concat [cpSyntax "⌊",cpSyntax "|_"]
           e ← pExp
           concat [cpSyntax "⌋",cpSyntax "_|"]
           return $ EmbedC e
      ]
  , fmixPrefix (𝕟64 10) $ do
      cpSyntax "let"
      cψ ← pCirPat
      cpSyntax "="
      ce ← pCirExp
      cpSyntax "in"
      return $ LetC cψ ce
  , fmixPrefix (𝕟64 10) $ do
      concat [cpSyntax "λ",cpSyntax "fun"]
      cψ ← pCirPat
      concat [cpSyntax "→",cpSyntax "->"]
      return $ LamC cψ
  , fmixInfixL (𝕟64 200) $ return AppC
  , fmixPostfix (𝕟64 100) $ do 
      cpSyntax "["
      φ ← pProt
      cpSyntax ":"
      ps ← pPrins
      cpSyntax "]"
      return $ \ ce → ShareC ce φ ps
  , fmixInfixL (𝕟64 50) $ do cpSyntax "+" ; return $ \ e₁ e₂ → PrimC "PLUS" $ list [e₁,e₂]
  , fmixInfixL (𝕟64 60) $ do cpSyntax "×" ; return $ \ e₁ e₂ → PrimC "TIMES" $ list [e₁,e₂]
  , fmixInfixL (𝕟64 60) $ do cpSyntax "/" ; return $ \ e₁ e₂ → PrimC "DIVIDE" $ list [e₁,e₂]
  , fmixInfix (𝕟64 40) $ do cpSyntax "<" ; return $ \ e₁ e₂ → PrimC "LT" $ list [e₁,e₂]
  , fmixInfix (𝕟64 40) $ do concat [cpSyntax "≤",cpSyntax "<="] ; return $ \ e₁ e₂ → PrimC "LTE" $ list [e₁,e₂]
  , fmixInfix (𝕟64 40) $ do concat [cpSyntax "≡",cpSyntax "=="] ; return $ \ e₁ e₂ → PrimC "EQ" $ list [e₁,e₂]
  ]

-------------
-- Pattern --
-------------

-- ψ ∈ pattern ⩴ x | • | ψ,ψ | _
type APat = Annotated FullContext Pat
data Pat =
    VarP 𝕏          -- x    /  x
  | BulP            -- •    /  ()
  | TupP APat APat  -- ψ,ψ  /  ψ,ψ
  | WildP           -- _    /  _
  deriving (Eq,Ord,Show)

pPat ∷ CParser TokenBasic APat
pPat = fmixfixWithContext "pattern" $ concat
  [ fmixTerminal $ concat
      [ do x ← cpName ; return $ VarP x
      , do concat [cpSyntax "•",cpSyntax "()"] ; return BulP
      , do cpSyntax "_" ; return WildP
      ]
  , fmixInfixL (𝕟64 20) $ do cpSyntax "," ; return TupP
  ]

-------------------
-- Program Terms --
-------------------

-- e ∈ term ⩴ i | b | d | s | x | •
--          | let x = e in e
--          | λ x ψ → e
--          | e e
--          | Λ α → e
--          | e@τ
--          | e,e
--          | if e then e else e
--          | e{P}
--          | e[φ:P]
--          | e⟨P⟩
--          | wfold e {x,x,x → e❵
--          | mpc{φ:P} e
--          | return e
--          | x ← e ; e
--          | circuit ce
type AExp = Annotated FullContext Exp
data Exp =
    IntE ℤ                        -- i                    /  i
  | BoolE 𝔹                       -- b                    /  b
  | DblE 𝔻                        -- d                    /  d
  | StrE 𝕊                        -- s                    /  s
  | VarE 𝕏                        -- x                    /  x
  | BulE                          -- •                    /  ()
  | LetE APat AExp AExp           -- let ψ = e in e       /  let ψ = e in e
  | LamE 𝕏 APat AExp              -- λ x ψ → e            /  fun x ψ → e
  | AppE AExp AExp                -- e e                  /  e e
  | TLamE (𝐿 𝕏) AExp              -- Λ α → e              /  abs α → e
  | TAppE AExp AType              -- e@τ                  /  e@τ
  | TupE AExp AExp                -- e,e                  /  e,e
  | IfE AExp AExp AExp            -- if e then e else e   /  if e then e else e
  | LocE AExp APrins              -- e{P}                 /  e{P}
  | ShareE AExp AProt APrins      -- e[φ:P]               /  e[φ:P]
  | BundleE AExp APrins           -- e⟨P⟩                 /  e<P>
  | WFold AExp 𝕏 APat APat AExp   -- wfold e {α,ψ,ψ → e}  /  wfold e {α,ψ,ψ -> e}
  | MPCE AProt APrins AExp        -- mpc{φ:P} e           /  mpc{φ:P} e
  | ReturnE AExp                  -- return e             /  return e
  | BindE APat AExp AExp          -- ψ ← e₁ ; e₂          /  ψ <- e₁ ; e₂
  | CircuitE ACirExp              -- circuit e            /  circuit e
  | NilE                          -- []                   /  []
  | ConsE AExp AExp               -- e ∷ e                /  e :: e
  | CaseE AExp (𝐿 (APat ∧ AExp))  -- case e {φ→e;…}       / case e {φ->e;…}
  | PrimE 𝕊 (𝐿 AExp)              -- φₓ[e,…,e]            /  φₓ[e,…,e]
  deriving (Eq,Ord,Show)

pExp ∷ CParser TokenBasic AExp
pExp = fmixfixWithContext "exp" $ concat
  [ fmixTerminal $ concat
      [ do i ← cpInteger ; return $ IntE i
      , do b ← pBool ; return $ BoolE b
      , do d ← cpDouble ; return $ DblE d
      , do s ← cpString ; return $ StrE s
      , do x ← cpName ; return $ VarE x
      , do concat [cpSyntax "•",cpSyntax "()"] ; return BulE
      , do cpSyntax "wfold"
           e₁ ← pExp
           cpSyntax "{"
           x ← cpName
           cpSyntax ","
           ψ₁ ← pPat
           cpSyntax ","
           ψ₂ ← pPat
           concat [cpSyntax "→",cpSyntax "->"]
           e₂ ← pExp
           cpSyntax "}"
           return $ WFold e₁ x ψ₁ ψ₂ e₂
      , do cpSyntax "circuit" ; ce ← pCirExp ; return $ CircuitE ce
      , do cpSyntax "[]" ; return NilE
      , do cpSyntax "case"
           e ← pExp
           cpSyntax "{"
           φes ← cpManySepBy (cpSyntax ";") $ do 
             φ ← pPat
             cpSyntax ";"
             e' ← pExp
             return $ φ :* e'
           cpSyntax "}"
           return $ CaseE e φes
      ]
  , fmixPrefix (𝕟64 10) $ do
      cpSyntax "let"
      ψ ← pPat
      cpSyntax "="
      e ← pExp
      cpSyntax "in"
      return $ LetE ψ e
  , fmixPrefix (𝕟64 10) $ do
      concat [cpSyntax "λ",cpSyntax "fun"]
      x ← cpName
      ψ ← pPat
      concat [cpSyntax "→",cpSyntax "->"]
      return $ LamE x ψ
  , fmixInfixL (𝕟64 200) $ return AppE
  , fmixPostfix (𝕟64 200) $ do
      cpSyntax "@"
      τ ← pType
      return $ \ e → TAppE e τ
  , fmixInfixL (𝕟64 20) $ do cpSyntax "," ; return TupE
  , fmixPrefix (𝕟64 10) $ do
      cpSyntax "if"
      e₁ ← pExp
      cpSyntax "then"
      e₂ ← pExp
      cpSyntax "else"
      return $ IfE e₁ e₂
  , fmixPostfix (𝕟64 100) $ do 
      cpSyntax "{"
      ps ← pPrins
      cpSyntax "}"
      return $ \ e → LocE e ps
  , fmixPostfix (𝕟64 100) $ do 
      cpSyntax "["
      φ ← pProt
      cpSyntax ":"
      ps ← pPrins
      cpSyntax "]"
      return $ \ e → ShareE e φ ps
  , fmixPostfix (𝕟64 100) $ do 
      cpSyntax "⟨"
      ps ← pPrins
      cpSyntax "⟩"
      return $ \ e → BundleE e ps
  , fmixPrefix (𝕟64 10) $ do
      cpSyntax "mpc"
      cpSyntax "{"
      φ ← pProt
      cpSyntax ":"
      ps ← pPrins
      cpSyntax "}"
      return $ MPCE φ ps
  , fmixPrefix (𝕟64 100) $ do cpSyntax "return" ; return ReturnE
  , fmixPrefix (𝕟64 10) $ do
      cpSyntax "do"
      ψ ← pPat
      concat [cpSyntax "←",cpSyntax "<-"]
      e ← pExp
      cpSyntax ";"
      return $ BindE ψ e
  , fmixInfixR (𝕟64 30) $ do concat [cpSyntax "∷",cpSyntax "::"] ; return ConsE
  , fmixInfixL (𝕟64 50) $ do cpSyntax "+" ; return $ \ e₁ e₂ → PrimE "PLUS" $ list [e₁,e₂]
  , fmixInfixL (𝕟64 60) $ do cpSyntax "×" ; return $ \ e₁ e₂ → PrimE "TIMES" $ list [e₁,e₂]
  , fmixInfixL (𝕟64 60) $ do cpSyntax "/" ; return $ \ e₁ e₂ → PrimE "DIVIDE" $ list [e₁,e₂]
  , fmixInfix (𝕟64 40) $ do cpSyntax "<" ; return $ \ e₁ e₂ → PrimE "LT" $ list [e₁,e₂]
  , fmixInfix (𝕟64 40) $ do concat [cpSyntax "≤",cpSyntax "<="] ; return $ \ e₁ e₂ → PrimE "LTE" $ list [e₁,e₂]
  , fmixInfix (𝕟64 40) $ do concat [cpSyntax "≡",cpSyntax "=="] ; return $ \ e₁ e₂ → PrimE "EQ" $ list [e₁,e₂]
  ]
      

makePrettySum ''CirExp
makePrettySum ''Pat
makePrettySum ''Exp

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

testParser ∷ IO ()
testParser = do
  s₁ ← read "examples/lib.psl"
  let ts₁ = tokens s₁
  ls₁ ← tokenizeIO lexer ts₁
  _tls₁ ← parseIO cpTLs ls₁
  out "lib done"
  s₂ ← read "examples/simple.psl"
  let ts₂ = tokens s₂
  ls₂ ← tokenizeIO lexer ts₂
  _tls₂ ← parseIO cpTLs ls₂
  out "file done"
