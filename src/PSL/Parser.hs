module PSL.Parser where

import UVMHS
import AddToUVMHS

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
levelCOND    = 𝕟64 20
levelCOMPARE = 𝕟64 30
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
      [ "(",")","{","}","[","]","⟨","⟩","<",">"
      , ".",",",":",";"
      , "→","->"
      , "⇒","=>"
      , "="
      , "_"
      , "⁇","??"
      , "@"
      , "⊆","c="
      ]
    kws = list
      [ "primitive"
      , "principal"
      , "trust"
      , "security"
      , "def"
      , "λ","fun"
      , "Λ","abs"
      , "∀","forall"
      , "let","in"
      , "if","then","else"
      , "case"
      , "reveal"
      , "share"
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
      , "par"
      ]
    ops = list 
      [ "•","()"
      , "[]"
      , "∷","::"
      , "⟨⟩","<>"
      , "+","-"
      , "×","*"
      , "/"
      , "≡","=="
      , "≤","<="
      , "⋖","<<"
      , "^"
      , "?"
      , "◇","><"
      , "true","false"
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
pKind = cpNewWithContextRendered "kind" $ concat
  [ do concat [cpSyntax "☆",cpSyntax "type"] ; return TypeK
  , do concat [cpSyntax "ℙ",cpSyntax "prin"] ; return PrinK
  , do concat [cpSyntax "ℙs",cpSyntax "prins"] ; return PrinsK
  ]

----------
-- Prin --
----------

pPrin ∷ CParser TokenBasic APrin
pPrin = cpNewWithContextRendered "prin" cpName

--------------
-- Prin-set --
--------------

pPrins ∷ CParser TokenBasic APrins
pPrins = cpNewWithContextRendered "prins" $ pow ^$ cpManySepBy (cpSyntax ",") pPrin

----------------
-- Constraint --
----------------

pConstr ∷ CParser TokenBasic AConstr
pConstr = cpNewWithContextRendered "constr" $ concat
  [ do cpSyntax "{"
       ps₁ ← pPrins
       cpSyntax "}"
       concat [cpSyntax "⊆",cpSyntax "<="]
       cpSyntax "{"
       ps₂ ← pPrins
       cpSyntax "}"
       return $ SubsetC ps₁ ps₂
  ]

------------
-- Effect --
------------

pEffect ∷ CParser TokenBasic AEffect
pEffect = cpNewWithContextRendered "effect" $ do
  (ps₁,ps₂) ← concat
    [ do cpSyntax "inp"
         cpSyntax ":"
         ps₁ ← pPrins
         ps₂O ← cpOptional $ do 
           cpSyntax ";"
           cpSyntax "rev"
           cpSyntax ":"
           pPrins
         return (ps₁,ifNone (Annotated null pø) ps₂O)
    , do cpSyntax "rev"
         cpSyntax ":"
         ps₂ ← pPrins
         return (Annotated null pø,ps₂)
    , return (Annotated null pø,Annotated null pø)
    ]
  return $ Effect ps₁ ps₂

----------
-- TVar --
----------

pTVar ∷ CParser TokenBasic ATVar
pTVar = cpNewWithContextRendered "tvar" cpName

----------
-- Type --
----------

pType ∷ CParser TokenBasic AType
pType = fmixfixWithContext "type" $ concat
  -- α
  [ fmixTerminal $ do x ← pTVar ; return $ VarT x
  -- 𝟙
  , fmixTerminal $ do concat [cpSyntax "𝟙",cpSyntax "unit"] ; return UnitT
  -- 𝔹
  , fmixTerminal $ do concat [cpSyntax "𝔹",cpSyntax "bool"] ; return 𝔹T
  -- 𝕊
  , fmixTerminal $ do concat [cpSyntax "𝕊",cpSyntax "string"] ; return 𝕊T
  -- ℕ[n.n]
  , fmixTerminal $ do
      concat [cpSyntax "ℕ",cpSyntax "nat"]
      nsO ← cpOptional $ do
        cpSyntax "["
        n₁ ← cpNatural
        n₂O ← cpOptional $ do
          cpSyntax "."
          cpNatural
        cpSyntax "]"
        return $ n₁ :* n₂O
      return $ ℕT $ elim𝑂 (Some (64 :* None)) Some nsO
  -- ℤ[n.n]
  , fmixTerminal $ do
      concat [cpSyntax "ℤ",cpSyntax "int"]
      nsO ← cpOptional $ do
        cpSyntax "["
        n₁ ← cpNatural
        n₂O ← cpOptional $ do
          cpSyntax "."
          cpNatural
        cpSyntax "]"
        return $ n₁ :* n₂O
      return $ ℤT $ elim𝑂 (Some (64 :* None)) Some nsO
  -- 𝔽[n]
  , fmixTerminal $ do
      concat [cpSyntax "𝔽",cpSyntax "float"]
      nO ← cpOptional $ do
        cpSyntax "["
        n ← cpNatural
        cpSyntax "]"
        return n
      return $ 𝔽T $ ifNone 64 nO
  -- τ + τ
  , fmixInfixL levelPLUS $ do concat [cpSyntax "+"] ; return (:+:)
  -- τ × τ
  , fmixInfixL levelTIMES $ do concat [cpSyntax "×",cpSyntax "*"] ; return (:×:)
  -- list τ
  , fmixPrefix levelAPP $ do cpSyntax "list" ; return ListT
  -- τ →{η} τ
  , fmixInfixR levelARROW $ do 
      Annotated cxt () ← cpNewExpressionContext $ cpWithContextRendered $ concat [cpSyntax "→",cpSyntax "->"] 
      ηO ← cpOptional $ do
        cpSyntax "{"
        η ← pEffect
        cpSyntax "}"
        return η
      let ps₀ = Annotated cxt pø
          η₀ = Annotated cxt $ Effect ps₀ ps₀
      return $ \ τ₁ τ₂ → τ₁ :→: (ifNone η₀ ηO :* τ₂)
  -- ∀ α:κ. [c,…,c] ⇒ τ
  , fmixPrefix levelLAM $ do
      concat [cpSyntax "∀", cpSyntax "forall"]
      α ← pTVar
      cpSyntax ":"
      κ ← pKind
      cpSyntax "."
      cs ← ifNone Nil ^$ cpOptional $ do
        cs ← cpManySepBy (cpSyntax ",") pConstr
        concat [cpSyntax "⇒",cpSyntax "=>"]
        return cs
      return $ ForallT α κ cs
  -- τ{P}
  , fmixPostfix levelMODE $ do 
      cpSyntax "{"
      p ← pPrin
      cpSyntax "}"
      return $ \ τ → SecT τ p
  -- τ{ssec:P}
  , fmixPostfix levelMODE $ do 
      cpSyntax "{"
      cpSyntax "ssec"
      cpSyntax ":"
      ps ← pPrins
      cpSyntax "}"
      return $ \ τ → SSecT τ ps
  -- τ{isec:P}
  , fmixPostfix levelMODE $ do 
      cpSyntax "{"
      cpSyntax "isec"
      cpSyntax ":"
      ps ← pPrins
      cpSyntax "}"
      return $ \ τ → ISecT τ ps
  -- τ{φ:P}
  , fmixPostfix levelMODE $ do 
      cpSyntax "{"
      φ ← pProt
      cpSyntax ":"
      ps ← pPrins
      cpSyntax "}"
      return $ \ τ → MPCT τ φ ps
  -- (τ)
  , fmixTerminal $ do cpSyntax "(" ; τ ← pType ; cpSyntax ")" ; return $ extract τ
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
pProt = cpNewWithContextRendered "prot" $ concat
  [ do cpSyntax "yao" ; return YaoP
  , do cpSyntax "bgw" ; return BGWP
  , do cpSyntax "gmw" ; return GMWP
  ]

---------
-- Var --
---------

pVar ∷ CParser TokenBasic AVar
pVar = cpNewWithContextRendered "var" cpName

-------------
-- Pattern --
-------------

pPat ∷ CParser TokenBasic APat
pPat = fmixfixWithContext "pattern" $ concat
  -- x
  [ fmixTerminal $ do x ← pVar ; return $ VarP x
  -- •
  , fmixTerminal $ do concat [cpSyntax "•",cpSyntax "()"] ; return BulP
  -- L ψ
  , fmixPrefix levelAPP $ do cpSyntax "L" ; return LP
  -- R ψ
  , fmixPrefix levelAPP $ do cpSyntax "R" ; return RP
  -- ψ,ψ
  , fmixInfixL levelCOMMA $ do cpSyntax "," ; return TupP
  -- []
  , fmixTerminal $ do cpSyntax "[]" ; return NilP
  -- ψ∷ψ
  , fmixInfixR levelCONS $ do concat [cpSyntax "∷",cpSyntax "::"] ; return ConsP
  -- ⟨⟩
  , fmixTerminal $ do concat [cpSyntax "⟨⟩",cpSyntax "<>"] ; return EmptyP
  -- ⟨ρ.ψ⟩⧺ψ
  , fmixPrefix levelPLUS $ do
      concat [cpSyntax "⟨",cpSyntax "<"]
      ρ ← pPrin
      cpSyntax "."
      ψ ← pPat
      concat [cpSyntax "⟩",cpSyntax ">"]
      concat [cpSyntax "⧺",cpSyntax "++"]
      return $ BundleP ρ ψ
  -- ψ : τ
  , fmixPostfix levelASCR $ do
      cpSyntax ":"
      τ ← pType
      return $ \ ψ → AscrP ψ τ
  -- _
  , fmixTerminal $ do cpSyntax "_" ; return WildP
  -- (ψ)
  , fmixTerminal $ do cpSyntax "(" ; ψ ← pPat ; cpSyntax ")" ; return $ extract ψ
  -- [ψ₁;…;ψₙ]
  , fmixTerminal $ do
      cpSyntax "["
      ψs ← cpManySepByContext cpWithContextRendered (cpSyntax ";") pPat
      a ← annotatedTag ^$ cpWithContextRendered $ cpSyntax "]"
      return $ extract $ foldrOnFrom ψs (Annotated a NilP) $ \ (Annotated a₁ ψ₁) ψ₂ → Annotated a₁ $ ConsP ψ₁ ψ₂
  -- ⟨ρ₁.ψ₁;…ρₙ.ψₙ⟩
  , fmixTerminal $ do
      do concat [cpSyntax "⟨",cpSyntax "<"]
         ψρs ← cpManySepByContext cpWithContextRendered (cpSyntax ";") $ do
           ρ ← pPrin
           cpSyntax "."
           ψ ← pPat
           return $ ρ :* ψ
         a ← annotatedTag ^$ cpWithContextRendered $ concat [cpSyntax "⟩",cpSyntax ">"]
         return $ extract $ foldOnFrom ψρs (Annotated a EmptyP) $ \ (Annotated a₁ (ρ₁ :* ψ₁)) ψ₂ → Annotated a₁ $ BundleP ρ₁ ψ₁ ψ₂
  ]

-------------------
-- Program Terms --
-------------------

pExp ∷ CParser TokenBasic AExp
pExp = fmixfixWithContext "exp" $ concat
  -- x
  [ fmixTerminal $ do x ← pVar ; return $ VarE x
  -- b
  , fmixTerminal $ do b ← pBool ; return $ BoolE b
  -- s
  , fmixTerminal $ do s ← cpString ; return $ StrE s
  -- i
  , fmixTerminal $ do i ← cpInteger ; return $ IntE i
  -- d
  , fmixTerminal $ do d ← cpDouble ; return $ FltE d
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
  -- rλ x ψ → e
  , fmixPrefix levelLAM $ do
      concat [cpSyntax "λ",cpSyntax "fun"]
      xO :* ψ ← concat
        [ do x ← pVar
             ψO ← cpOptional pPat
             return $ case ψO of
               None → None :* siphon x (VarP x)
               Some ψ → Some x :* ψ
        , do ψ ← pPat
             return $ None :* ψ
        ]
      concat [cpSyntax "→",cpSyntax "->"]
      return $ LamE xO ψ
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
    ρ ← pPrin
    cpSyntax "}"
    return $ SoloE ρ
  -- {par:P} e
  , fmixPrefix levelPAR $ do 
      cpSyntax "{"
      cpSyntax "par"
      cpSyntax ":"
      ps ← pPrins
      cpSyntax "}"
      return $ ParE ps
  -- share{φ:P} e
  , fmixPrefix levelAPP $ do 
      cpSyntax "share" 
      cpSyntax "{"
      φ ← pProt
      cpSyntax ":"
      ps ← pPrins
      cpSyntax "}"
      return $ ShareE φ ps
  -- e.ρ
  , fmixPostfix levelACCESS $ do cpSyntax "." ; ρ ← pPrin ; return $ \ e → AccessE e ρ
  -- ⟨ρ₁.e₁;…;ρₙ;eₙ⟩
  , fmixTerminal $ do
      concat [cpSyntax "⟨",cpSyntax "<"]
      ρes ← cpManySepBy (cpSyntax ";") $ do
        ρ ← pPrin
        cpSyntax "."
        e ← pExp
        return $ ρ :* e
      concat [cpSyntax "⟩",cpSyntax ">"]
      return $ BundleE ρes
  -- e⧺e
  , fmixInfixL levelPLUS $ do concat [cpSyntax "⧺",cpSyntax "++"] ; return BundleUnionE
  -- reveal{P} e
  , fmixPrefix levelMPC $ do
      cpSyntax "reveal"
      cpSyntax "{"
      ps ← pPrins
      cpSyntax "}"
      return $ RevealE ps
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
  -- prim[⊙](e,…,e)
  , fmixInfixL levelPLUS $ do concat [cpSyntax "∨",cpSyntax "||"] ; return $ \ e₁ e₂ → PrimE "OR" $ list [e₁,e₂]
  , fmixInfixL levelTIMES $ do concat [cpSyntax "∧",cpSyntax "&&"] ; return $ \ e₁ e₂ → PrimE "AND" $ list [e₁,e₂]
  , fmixInfixL levelPLUS $ do cpSyntax "+" ; return $ \ e₁ e₂ → PrimE "PLUS" $ list [e₁,e₂]
  , fmixInfixL levelPLUS $ do cpSyntax "-" ; return $ \ e₁ e₂ → PrimE "MINUS" $ list [e₁,e₂]
  , fmixInfixL levelTIMES $ do concat [cpSyntax "×",cpSyntax "*"] ; return $ \ e₁ e₂ → PrimE "TIMES" $ list [e₁,e₂]
  , fmixInfixL levelTIMES $ do cpSyntax "/" ; return $ \ e₁ e₂ → PrimE "DIVIDE" $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do concat [cpSyntax "⋖",cpSyntax "<<"] ; return $ \ e₁ e₂ → PrimE "LT" $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do concat [cpSyntax "≤",cpSyntax "<="] ; return $ \ e₁ e₂ → PrimE "LTE" $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do concat [cpSyntax "≡",cpSyntax "=="] ; return $ \ e₁ e₂ → PrimE "EQ" $ list [e₁,e₂]
  , fmixInfixR levelCOND $ do
      cpSyntax "?"
      e₂ ← pExp
      concat [cpSyntax "◇",cpSyntax "><"]
      return $ \ e₁ e₃ → PrimE "COND" $ list [e₁,e₂,e₃]
  ]
      
---------------
-- Top-level --
---------------

pTL ∷ CParser TokenBasic ATL
pTL = cpNewWithContextRendered "tl" $ concat
  [ do cpSyntax "def"
       x ← pVar
       concat
         [ do cpSyntax ":"
              ηO ← cpOptional $ do
                cpSyntax "{"
                η ← pEffect
                cpSyntax "}"
                return η
              τ ← pType
              let η = ifNone (Annotated null $ Effect (Annotated null pø) (Annotated null pø)) ηO
              return $ DeclTL x η τ
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
       x ← pVar
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
