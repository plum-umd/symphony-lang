module PSL.Parser where

import UVMHS
-- import AddToUVMHS

import PSL.Syntax

levelIF,levelLAM,levelLET ∷ ℕ64
levelIF   = 𝕟64 10
levelLAM  = 𝕟64 10
levelLET  = 𝕟64 10

levelCOMMA,levelCONS,levelMPC,levelPAR,levelASCR ∷ ℕ64

levelCOMMA   = 𝕟64 20
levelCONS    = 𝕟64 21
levelMPC     = 𝕟64 24
levelPAR     = 𝕟64 25
levelASCR    = 𝕟64 29

levelCOND,levelCOMPARE,levelARROW,levelPLUS,levelTIMES ∷ ℕ64
levelCOND    = 𝕟64 30
levelCOMPARE = 𝕟64 35
levelARROW   = 𝕟64 40
levelPLUS    = 𝕟64 50
levelTIMES   = 𝕟64 60

levelAPP ∷ ℕ64
levelAPP = 𝕟64 100

levelCIRCUIT,levelACCESS ∷ ℕ64
levelCIRCUIT = 𝕟64 120
levelACCESS  = 𝕟64 130

levelMODE ∷ ℕ64
levelMODE  = 𝕟64 200

lexer ∷ Lexer CharClass ℂ TokenClassBasic ℕ64 TokenBasic
lexer = lexerBasic puns kws prim ops
  where
    puns = list 
      [ "(",")","{","}","[","]"
      , "⟪","<<"
      , "⟫",">>"
      , ".",",",":",";"
      , "→","->"
      , "⇒","=>"
      , "="
      , "_"
      , "⁇","??"
      , "@"
      , "⊆","c="
      , "#"
      , "|"
      ]
    kws = list
      [ "primitive"
      , "principal"
      , "def"
      , "λ","fun"
      , "Λ","abs"
      , "∀","forall"
      , "let","in"
      , "if","then","else"
      , "case"
      , "reveal"
      , "share"
      , "trace"
      , "set"
      ]
    prim = list
      [ "yao","gmw","bgw"
      , "ssec","isec"
      , "☆","type"
      , "ℙ","prin"
      , "𝟘","empty"
      , "𝟙","unit"
      , "𝔹","bool"
      , "𝕊","string"
      , "ℕ","nat"
      , "ℤ","int"
      , "𝔽","flt"
      , "list"
      , "read"
      , "inp","rev"
      , "par","sec"
      , "∞","inf"
      , "⊤","all"
      ]
    ops = list 
      [ "•","()"
      , "[]"
      , "∷","::"
      , "⧺","++"
      , "⟪⟫","<<>>"
      , "+","-"
      , "×","*"
      , "/","%"
      , "≡","=="
      , "<",">"
      , "≤","<="
      , "≥",">="
      , "^"
      , "?"
      , "◇","><"
      , "||","∨"
      , "&&","∧"
      , "true","false"
      , "L","R"
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

pKind ∷ CParser TokenBasic Kind
pKind = cpNewContext "kind" $ concat
  [ do concat [cpSyntax "☆",cpSyntax "type"] ; return TypeK
  , do concat [cpSyntax "ℙ",cpSyntax "prin"] ; return PrinK
  , do concat [cpSyntax "ℙs",cpSyntax "prins"] ; return PrinsK
  ]

----------
-- Prin --
----------

pPrin ∷ CParser TokenBasic 𝕏
pPrin = cpNewContext "prin" cpName

pPrinExp ∷ CParser TokenBasic PrinExp
pPrinExp = cpNewContext "prin-exp" $ do
  ρ ← pPrin
  nO ← cpOptional $ do
    cpSyntax "."
    natΩ ^$ cpInteger
  return $ case nO of
    None → VarPE ρ
    Some n → AccessPE ρ n

--------------
-- Prin-set --
--------------

pPrins ∷ CParser TokenBasic (𝐿 PrinExp)
pPrins = cpManySepBy (cpSyntax ",") pPrinExp

pPrinExps ∷ CParser TokenBasic (𝐿 PrinExp)
pPrinExps = cpManySepBy (cpSyntax ",") pPrinExp

----------------
-- Constraint --
----------------

pConstr ∷ CParser TokenBasic Constr
pConstr = cpNewContext "constr" $ do
  do ρs₁ ← concat
       [ do cpSyntax "{"
            ρs₁ ← pPrins
            cpSyntax "}"
            return ρs₁
       , do single ^$ pPrinExp
       ]
     concat [cpSyntax "⊆",cpSyntax "<="]
     ρs₂ ← concat
       [ do cpSyntax "{"
            ρs₂ ← pPrins
            cpSyntax "}"
            return ρs₂
       , do single ^$ pPrinExp
       ]
     return $ SubsetC ρs₁ ρs₂

------------
-- Effect --
------------

pEMode ∷ CParser TokenBasic EMode
pEMode = cpNewContext "effect-mode" $ concat
  [ do cpSyntax "par"
       cpSyntax ":"
       ρs ← pPrins
       return $ PSecEM ρs
  , do cpSyntax "sec"
       cpSyntax ":"
       ρs ← pPrins
       return $ SSecEM ρs
  , do concat [cpSyntax "⊤",cpSyntax "all"]
       return TopEM
  ]

pEffect ∷ CParser TokenBasic Effect
pEffect = cpNewContext "effect" $ do
  (ρs₁,ρs₂,em) ← concat
    [ do cpSyntax "inp"
         cpSyntax ":"
         ρs₁ ← pow ^$ pPrins
         ρs₂O ← cpOptional $ do 
           cpSyntax ";"
           cpSyntax "rev"
           cpSyntax ":"
           pow ^$ pPrins
         emO ← cpOptional $ do
          cpSyntax ";"
          pEMode
         return (ρs₁,ifNone null ρs₂O,ifNone TopEM emO)
    , do cpSyntax "rev"
         cpSyntax ":"
         ρs₂ ← pow ^$ pPrins
         emO ← cpOptional $ do
          cpSyntax ";"
          pEMode
         return (null,ρs₂,ifNone TopEM emO)
    , do em ← pEMode
         return (null,null,em)
    , do return (null,null,TopEM)
    ]
  return $ Effect ρs₁ ρs₂ em

----------
-- TVar --
----------

pTVar ∷ CParser TokenBasic TVar
pTVar = cpNewContext "tvar" cpName

---------------
-- Precision --
---------------

pIPrecision ∷ CParser TokenBasic IPrecision
pIPrecision = ifNone iprDefault ^$ cpOptional $ do
  cpSyntax "#"
  concat
    [ do n₁ ← natΩ ^$ cpInteger
         n₂ ← ifNone 0 ^$ cpOptional $ do
           cpSyntax "."
           natΩ ^$ cpInteger
         return $ FixedIPr n₁ n₂
    , do concat [cpSyntax "∞",cpSyntax "inf"]
         return InfIPr
    ]

pFPrecision ∷ CParser TokenBasic FPrecision
pFPrecision = ifNone fprDefault ^$ cpOptional $ do
  cpSyntax "#"
  n ← natΩ ^$ cpInteger
  return $ FixedFPr n

----------
-- Type --
----------

pType ∷ CParser TokenBasic Type
pType = cpNewContext "type" $ mixfix $ concat
  -- α
  [ mixTerminal $ do x ← pTVar ; return $ VarT x
  -- 𝟙
  , mixTerminal $ do concat [cpSyntax "𝟙",cpSyntax "unit"] ; return UnitT
  -- 𝔹
  , mixTerminal $ do concat [cpSyntax "𝔹",cpSyntax "bool"] ; return 𝔹T
  -- 𝕊
  , mixTerminal $ do concat [cpSyntax "𝕊",cpSyntax "string"] ; return 𝕊T
  -- ℙ
  , mixTerminal $ do concat [cpSyntax "ℙ",cpSyntax "prin"] ; return ℙT
  -- ℕ#n.n
  , mixTerminal $ do
      concat [cpSyntax "ℕ",cpSyntax "nat"]
      pr ← pIPrecision
      return $ ℕT pr
  -- ℤ#n.n
  , mixTerminal $ do
      concat [cpSyntax "ℤ",cpSyntax "int"]
      pr ← pIPrecision
      return $ ℤT pr
  -- 𝔽#n
  , mixTerminal $ do
      concat [cpSyntax "𝔽",cpSyntax "float"]
      pr ← pFPrecision
      return $ 𝔽T pr
  -- τ + τ
  , mixInfixL levelPLUS $ do concat [cpSyntax "+"] ; return (:+:)
  -- τ × τ
  , mixInfixL levelTIMES $ do concat [cpSyntax "×",cpSyntax "*"] ; return (:×:)
  -- list τ
  , mixPrefix levelAPP $ do cpSyntax "list" ; return ListT
  -- τ →{η} τ
  , mixInfixR levelARROW $ do 
      concat [cpSyntax "→",cpSyntax "->"] 
      ηO ← cpOptional $ do
        cpSyntax "{"
        η ← pEffect
        cpSyntax "}"
        return η
      let η₀ = Effect null null TopEM
      return $ \ τ₁ τ₂ → τ₁ :→: (ifNone η₀ ηO :* τ₂)
  -- (x : τ | c,…,c) →{η} τ
  , mixPrefix levelARROW $ do
      cpSyntax "("
      x ← pVar
      cpSyntax ":"
      τ₁ ← pType
      cs ← ifNone Nil ^$ cpOptional $ do
        cpSyntax "|"
        cpManySepBy (cpSyntax ",") pConstr
      cpSyntax ")"
      concat [cpSyntax "→",cpSyntax "->"]
      ηO ← cpOptional $ do
        cpSyntax "{"
        η ← pEffect
        cpSyntax "}"
        return η
      let η₀ = Effect null null TopEM
      return $ \ τ₂ → (x :* τ₁ :* cs) :→†: (ifNone η₀ ηO :* τ₂)
  -- ∀ α:κ,…,α:κ . c,…,c ⇒ τ
  , mixPrefix levelLAM $ do
      concat [cpSyntax "∀", cpSyntax "forall"]
      ακs ← cpManySepBy (cpSyntax ",") $ do
        α ← pTVar
        cpSyntax ":"
        κ ← pKind
        return $ α :* κ
      cs ← ifNone Nil ^$ cpOptional $ do
        cpSyntax "|"
        cpManySepBy (cpSyntax ",") pConstr
      cpSyntax "."
      return $ ForallT ακs cs
  -- τ{ρ}
  , mixPostfix levelMODE $ do 
      cpSyntax "{"
      ρe ← pPrinExp
      cpSyntax "}"
      return $ SecT ρe
  -- τ{ssec:P}
  , mixPostfix levelMODE $ do 
      cpSyntax "{"
      cpSyntax "ssec"
      cpSyntax ":"
      ρes ← pow ^$ pPrinExps
      cpSyntax "}"
      return $ SSecT ρes
  -- τ{isec:P}
  , mixPostfix levelMODE $ do 
      cpSyntax "{"
      cpSyntax "isec"
      cpSyntax ":"
      ρes ← pow ^$ pPrinExps
      cpSyntax "}"
      return $ ISecT ρes
  -- τ{φ:P}
  , mixPostfix levelMODE $ do 
      cpSyntax "{"
      φ ← pProt
      cpSyntax ":"
      ρes ← pow ^$ pPrinExps
      cpSyntax "}"
      return $ ShareT φ ρes
  -- (τ)
  , mixTerminal $ do cpSyntax "(" ; τ ← pType ; cpSyntax ")" ; return τ
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

pProt ∷ CParser TokenBasic Prot
pProt = cpNewContext "prot" $ concat
  [ do cpSyntax "yao" ; return YaoP
  , do cpSyntax "bgw" ; return BGWP
  , do cpSyntax "gmw" ; return GMWP
  ]

---------
-- Var --
---------

pVar ∷ CParser TokenBasic Var
pVar = cpNewContext "var" cpName

-------------
-- Pattern --
-------------

pPat ∷ CParser TokenBasic Pat
pPat = mixfix $ concat
  -- x
  [ mixTerminal $ do x ← pVar ; return $ VarP x
  -- •
  , mixTerminal $ do concat [cpSyntax "•",cpSyntax "()"] ; return BulP
  -- L ψ
  , mixPrefix levelAPP $ do cpSyntax "L" ; return LP
  -- R ψ
  , mixPrefix levelAPP $ do cpSyntax "R" ; return RP
  -- ψ,ψ
  , mixInfixL levelCOMMA $ do cpSyntax "," ; return TupP
  -- []
  , mixTerminal $ do cpSyntax "[]" ; return NilP
  -- ψ∷ψ
  , mixInfixR levelCONS $ do concat [cpSyntax "∷",cpSyntax "::"] ; return ConsP
  -- ⟪⟫
  , mixTerminal $ do concat [cpSyntax "⟪⟫",cpSyntax "<<>>"] ; return EmptyP
  -- ⟪ρ.ψ⟫⧺ψ
  , mixPrefix levelPLUS $ do
      concat [cpSyntax "⟪",cpSyntax "<<"]
      ρ ← pPrin
      cpSyntax "."
      ψ ← pPat
      concat [cpSyntax "⟫",cpSyntax ">>"]
      concat [cpSyntax "⧺",cpSyntax "++"]
      return $ BundleP ρ ψ
  -- ψ : τ
  , mixPostfix levelASCR $ do
      cpSyntax ":"
      τ ← pType
      return $ \ ψ → AscrP ψ τ
  -- _
  , mixTerminal $ do cpSyntax "_" ; return WildP
  -- (ψ)
  , mixTerminal $ do cpSyntax "(" ; ψ ← pPat ; cpSyntax ")" ; return ψ
  -- [ψ₁;…;ψₙ]
  , mixTerminal $ do
      cpSyntax "["
      -- ψs ← cpManySepByContext cpWithContextRendered (cpSyntax ";") pPat
      ψs ← cpManySepBy (cpSyntax ";") pPat
      cpSyntax "]"
      return $ foldrOnFrom ψs NilP $ \ ψ₁ ψ₂ → ConsP ψ₁ ψ₂
  -- ⟪ρ₁.ψ₁;…ρₙ.ψₙ⟫
  , mixTerminal $ do
      do concat [cpSyntax "⟪",cpSyntax "<<"]
         ψρs ← cpManySepBy (cpSyntax ";") $ do
           ρ ← pPrin
           cpSyntax "."
           ψ ← pPat
           return $ ρ :* ψ
         concat [cpSyntax "⟫",cpSyntax ">>"]
         return $ foldOnFrom ψρs EmptyP $ \ (ρ₁ :* ψ₁) ψ₂ → BundleP ρ₁ ψ₁ ψ₂
  ]

-------------------
-- Program Terms --
-------------------

pExp ∷ CParser TokenBasic Exp
pExp = fmixfixWithContext "exp" $ concat
  -- x
  [ fmixTerminal $ do x ← pVar ; return $ VarE x
  -- b
  , fmixTerminal $ do b ← pBool ; return $ BoolE b
  -- s
  , fmixTerminal $ do s ← cpString ; return $ StrE s
  -- n#n.n
  , fmixTerminal $ do 
      n ← cpNatural 
      pr ← pIPrecision
      return $ NatE pr n
  -- i#n.n
  , fmixTerminal $ do 
      i ← cpInteger 
      pr ← pIPrecision
      return $ IntE pr i
  -- d#n
  , fmixTerminal $ do 
      d ← cpDouble 
      pr ← pFPrecision
      return $ FltE pr d
  -- •
  , fmixTerminal $ do concat [cpSyntax "•",cpSyntax "()"] ; return BulE
  -- if e then e else e
  , fmixPrefix levelIF $ do
      cpSyntax "if"
      e₁ ← pExp
      cpSyntax "then"
      e₂ ← pExp
      cpSyntax "else"
      return $ IfE e₁ e₂
  -- L e
  , fmixPrefix levelAPP $ do cpSyntax "L" ; return LE
  -- R e
  , fmixPrefix levelAPP $ do cpSyntax "R" ; return RE
  -- e,e
  , fmixInfixL levelCOMMA $ do cpSyntax "," ; return TupE
  -- []
  , fmixTerminal $ do cpSyntax "[]" ; return NilE
  -- e∷e
  , fmixInfixR levelCONS $ do concat [cpSyntax "∷",cpSyntax "::"] ; return ConsE
  -- let ψ : τ in e
  , fmixPrefix levelLET $ do
      cpSyntax "let"
      x ← pVar
      cpSyntax ":"
      τ ← pType
      void $ cpOptional $ cpSyntax "in"
      return $ LetTyE x τ
  -- let ψ = e in e
  , fmixPrefix levelLET $ do
      cpSyntax "let"
      ψ ← pPat
      cpSyntax "="
      e ← pExp
      void $ cpOptional $ cpSyntax "in"
      return $ LetE ψ e
  -- case e {ψ→e;…;ψ→e}
  , fmixTerminal $ do 
      cpSyntax "case"
      e ← pExp
      cpSyntax "{"
      φes ← cpManySepBy (cpSyntax ";") $ do 
        φ ← pPat
        concat [cpSyntax "→",cpSyntax "->"]
        e' ← pExp
        return $ φ :* e'
      cpSyntax "}"
      return $ CaseE e φes
  -- λ [x] ψ…ψ → e
  , fmixPrefix levelLAM $ do
      concat [cpSyntax "λ",cpSyntax "fun"]
      xO ← cpOptional $ do
        cpSyntax "["
        x ← pVar
        cpSyntax "]"
        return x
      ψs ← cpMany pPat
      concat [cpSyntax "→",cpSyntax "->"]
      return $ LamE xO ψs
  -- e e
  , fmixInfixL levelAPP $ return AppE
  -- Λ α → e
  , fmixPrefix levelLAM $ do
      concat [cpSyntax "Λ",cpSyntax "abs"]
      α ← pTVar
      concat [cpSyntax "→",cpSyntax "->"]
      return $ TLamE α
  -- e @ τ
  , fmixPostfix levelAPP $ do
      cpSyntax "@"
      τ ← pType
      return $ \ e → TAppE e τ
  -- {ρ} e
  , fmixPrefix levelPAR $ do
    cpSyntax "{"
    ρes ← pPrinExps
    cpSyntax "}"
    return $ SoloE ρes
  -- {par:P} e
  , fmixPrefix levelPAR $ do 
      cpSyntax "{"
      cpSyntax "par"
      cpSyntax ":"
      ρes ← pPrinExps
      cpSyntax "}"
      return $ ParE ρes
  -- share{φ:P} e
  , fmixPrefix levelAPP $ do 
      cpSyntax "share" 
      cpSyntax "{"
      φ ← pProt
      cpSyntax ":"
      ρes ← pPrinExps
      cpSyntax "}"
      return $ ShareE φ ρes
  -- e.ρ
  , fmixPostfix levelACCESS $ do cpSyntax "." ; ρe ← pPrinExp ; return $ \ e → AccessE e ρe
  -- ⟪ρ₁.e₁;…;ρₙ;eₙ⟫
  , fmixTerminal $ do
      concat [cpSyntax "⟪",cpSyntax "<<"]
      ρes ← cpManySepBy (cpSyntax ";") $ do
        ρe ← pPrinExp
        cpSyntax "."
        e ← pExp
        return $ ρe :* e
      concat [cpSyntax "⟫",cpSyntax ">>"]
      return $ BundleE ρes
  -- e⧺e
  , fmixInfixL levelPLUS $ do concat [cpSyntax "⧺",cpSyntax "++"] ; return BundleUnionE
  -- reveal{P} e
  , fmixPrefix levelLET $ do
      cpSyntax "reveal"
      cpSyntax "{"
      ρes ← pPrinExps
      cpSyntax "}"
      return $ RevealE ρes
  -- e:τ
  , fmixPostfix levelASCR $ do
      cpSyntax ":"
      τ ← pType
      return $ \ e → AscrE e τ
  -- read τ
  , fmixPrefix levelAPP $ do
      cpSyntax "read"
      τ ← pType
      return $ ReadE τ
  -- _
  , fmixTerminal $ do cpSyntax "_" ; return InferE
  -- ⁇
  , fmixTerminal $ do cpSyntax "??" ; return HoleE
  -- (e)
  , fmixTerminal $ do cpSyntax "(" ; e ← pExp ; cpSyntax ")" ; return $ extract e
  -- [e₁;…;eₙ]
  , fmixTerminal $ do
      cpSyntax "["
      es ← cpManySepByContext cpWithContextRendered (cpSyntax ";") pExp
      a ← annotatedTag ^$ cpWithContextRendered $ cpSyntax "]"
      return $ extract $ foldrOnFrom es (Annotated a NilE) $ \ (Annotated a₁ e₁) e₂ → Annotated a₁ $ ConsE e₁ e₂
  , fmixTerminal $ do
      cpSyntax "set"
      cpSyntax "("
      ρes ← pPrinExps
      cpSyntax ")"
      return $ SetE ρes
  -- prim[⊙](e,…,e)
  , fmixInfixL levelPLUS $ do concat [cpSyntax "∨",cpSyntax "||"] ; return $ \ e₁ e₂ → PrimE "OR" $ list [e₁,e₂]
  , fmixInfixL levelTIMES $ do concat [cpSyntax "∧",cpSyntax "&&"] ; return $ \ e₁ e₂ → PrimE "AND" $ list [e₁,e₂]
  , fmixInfixL levelPLUS $ do cpSyntax "+" ; return $ \ e₁ e₂ → PrimE "PLUS" $ list [e₁,e₂]
  , fmixInfixL levelPLUS $ do cpSyntax "-" ; return $ \ e₁ e₂ → PrimE "MINUS" $ list [e₁,e₂]
  , fmixInfixL levelTIMES $ do concat [cpSyntax "×",cpSyntax "*"] ; return $ \ e₁ e₂ → PrimE "TIMES" $ list [e₁,e₂]
  , fmixInfixL levelTIMES $ do cpSyntax "/" ; return $ \ e₁ e₂ → PrimE "DIVIDE" $ list [e₁,e₂]
  , fmixInfixL levelTIMES $ do cpSyntax "%" ; return $ \ e₁ e₂ → PrimE "MOD" $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do concat [cpSyntax "≡",cpSyntax "=="] ; return $ \ e₁ e₂ → PrimE "EQ" $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do cpSyntax "<" ; return $ \ e₁ e₂ → PrimE "LT" $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do cpSyntax ">" ; return $ \ e₁ e₂ → PrimE "GT" $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do concat [cpSyntax "≤",cpSyntax "<="] ; return $ \ e₁ e₂ → PrimE "LTE" $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do concat [cpSyntax "≥",cpSyntax ">="] ; return $ \ e₁ e₂ → PrimE "GTE" $ list [e₁,e₂]
  , fmixInfixR levelCOND $ do
      cpSyntax "?"
      e₂ ← pExp
      concat [cpSyntax "◇",cpSyntax "><"]
      return $ \ e₁ e₃ → PrimE "COND" $ list [e₁,e₂,e₃]
  , fmixPrefix levelLET $ do
      cpSyntax "trace"
      e₁ ← pExp
      void $ cpOptional $ cpSyntax "in"
      return $ TraceE e₁
  ]
      
---------------
-- Top-level --
---------------

pTL ∷ CParser TokenBasic TL
pTL = cpNewWithContextRendered "tl" $ concat
  [ do cpSyntax "def"
       x ← pVar
       ψs ← cpMany pPat
       concat
         [ do cpSyntax ":"
              τ ← pType
              return $ DeclTL x τ
         , do cpSyntax "="
              e ← pExp
              return $ DefnTL x ψs e
         ]
  , do cpSyntax "principal"
       ρds ← cpOneOrMore $ do
         ρ ← 𝕩name ^$ pPrin
         nO ← cpOptional $ do
           cpSyntax "["
           n ← natΩ ^$ cpInteger
           cpSyntax "]"
           return n
         return $ case nO of
           None → SinglePD ρ
           Some n → ArrayPD ρ n
       return $ PrinTL ρds
  , do cpSyntax "primitive"
       x ← pVar
       cpSyntax ":"
       τ ← pType
       return $ PrimTL x τ
  ]

cpTLs ∷ CParser TokenBasic (𝐿 TL)
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
