module PSL.Parser where

import UVMHS
import AddToUVMHS

import PSL.Syntax

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
      , "read"
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

pKind ∷ CParser TokenBasic AKind
pKind = cpNewContext "kind" $ cpWithContextRendered $ concat
  [ do concat [cpSyntax "☆",cpSyntax "type"] ; return TypeK
  , do concat [cpSyntax "ℙ",cpSyntax "prin"] ; return PrinK
  ]

----------
-- Prin --
----------

pPrin ∷ CParser TokenBasic APrin
pPrin = cpNewContext "prin" $ cpWithContextRendered cpName

--------------
-- Prin-set --
--------------

pPrins ∷ CParser TokenBasic APrins
pPrins = cpNewContext "prins" $ cpWithContextRendered $ pow ^$ cpManySepBy (cpSyntax ",") pPrin

------------
-- Scheme --
------------

pScheme ∷ CParser TokenBasic AScheme
pScheme = cpNewContext "scheme" $ cpWithContextRendered $ concat
  [ do cpSyntax "nshare" ; return NoS
  , do cpSyntax "gshare" ; return GMWS
  , do cpSyntax "yshare" ; return YaoS
  , do cpSyntax "sshare" ; return ShamirS
  ]

-----------------
-- Circuit Ops --
-----------------

pCirOps ∷ CParser TokenBasic ACirOps
pCirOps = cpNewContext "cir-ops" $ cpWithContextRendered $ concat
  [ do cpSyntax "ncir" ; return NoCO
  , do cpSyntax "bcir" ; return BoolCO
  , do cpSyntax "acir" ; return ArithCO
  , do cpSyntax "ccir" ; return CompCO
  , do cpSyntax "ucir" ; return UnivCO
  ]

----------------
-- Constraint --
----------------

pConstr ∷ CParser TokenBasic AConstr
pConstr = cpNewContext "constr" $ cpWithContextRendered $ concat
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
             Annotated cxt () ← cpNewExpressionContext $ cpWithContextRendered $ cpSyntax ":"
             σ ← ifNone (Annotated cxt NoS) ^$ cpOptional $ do
                 σ ← pScheme
                 cpSyntax ":"
                 return σ
             return $ ς :* σ
        , do σ ← pScheme
             Annotated cxt () ← cpNewExpressionContext $ cpWithContextRendered $ cpSyntax ":"
             return $ Annotated cxt NoCO :* σ
        ]
      ps ← pPrins
      cpSyntax "}"
      return $ \ τ → CirT τ ς σ ps
  , fmixPrefix levelMPCTY $ do
      cpSyntax "MPC"
      cpSyntax "{"
      ps ← pPrins
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

pProt ∷ CParser TokenBasic AProt
pProt = cpNewContext "pProt" $ cpWithContextRendered $ concat
  [ do cpSyntax "yao" ; return YaoP
  , do cpSyntax "bgw" ; return BGWP
  , do cpSyntax "gmw" ; return GMWP
  , do cpSyntax "none" ; return NoneP
  ]

-------------
-- Pattern --
-------------

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
      , do
        cpSyntax "read"
        cpSyntax "["
        τ ← pType
        cpSyntax "]"
        return $ ReadE τ
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
      
---------------
-- Top-level --
---------------

pTL ∷ CParser TokenBasic ATL
pTL = cpNewContext "tl" $ cpWithContextRendered $ concat
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

testParserExample ∷ 𝕊 → IO ()
testParserExample fn = do
  s ← read $ "examples/" ⧺ fn ⧺ ".psl"
  let ts = tokens s
  ls ← tokenizeIO lexer ts
  _tls ← parseIO cpTLs ls
  out $ "DONE: " ⧺ fn

testParser ∷ IO ()
testParser = do
  testParserExample "e1"
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
