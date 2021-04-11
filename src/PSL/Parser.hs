module PSL.Parser where

import UVMHS
-- import AddToUVMHS

import PSL.Syntax
import PSL.Interpreter.Pretty

cpSyntaxVoid ∷ 𝕊 -> CParser TokenBasic ()
cpSyntaxVoid = void ∘ cpSyntax

lexer ∷ Lexer CharClass ℂ TokenClassBasic ℕ64 TokenBasic
lexer = lexerBasic puns kws prim ops
  where
    puns = list
      [ "(",")","{","}","[","]"
      , "⟪","<<"
      , "⟫",">>"
      , ".",",",":",";"
      , "→","->"
      , "←","<-"
      , "⇒","=>"
      , "="
      , "_"
      , "⁇","??"
      , "@"
      , "⊆","c="
      , "#"
      , "|"
      , "!","≔",":="
      , "⊥","_|_"
      ]
    kws = list
      [ "primitive"
      , "principal"
      , "def","sec"
      , "λ","fun"
      , "Λ","abs"
      , "∀","forall"
      , "let","in"
      , "if","mux","then","else"
      , "case"
      , "reveal"
      , "share"
      , "send"
      , "trace"
      , "set"
      , "this"
      , "solo","as"
      , "fold","on"
      , "par"
      , "do"
      , "read","write","from","to"
      , "proc","return"
      , "loop"
      , "when"
      , "import","with"
      , "nizk-witness","nizk-commit"
      , "virtual","party"
      , "sign","unsign"
      , "is-signed"
      ]
    prim = list
      [ "plain","yao","yaoN","yao2","gmw","bgw","bgv","spdz","auto"
      , "ssec","isec","bundle"
      , "☆","type"
      , "ℙ","prin"
      , "ℙs","prins"
      , "𝟘","empty"
      , "𝟙","unit"
      , "𝔹","bool"
      , "𝕊","string"
      , "ℕ","nat"
      , "ℤ","int"
      , "𝔽","flt"
      , "list"
      , "ref","array"
      , "rand","rand-range"
      , "inp","rev"
      , "∞","inf"
      , "⊤","all"
      , "nizk-test","nizk-verify"
      ]
    ops = list
      [ "•","()"
      , "[]"
      , "∷","::"
      , "⧺","++"
      , "∪","\\/"
      , "⟪⟫","<<>>"
      , "{}"
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
      , "not","¬"
      , "||","∨"
      , "&&","∧"
      , "true","false"
      , "L","R"
      , "abs_val"
      , "ceil"
      , "sqrt"
      , "log_base_2"
      , "size"
      , "⧻", "+++"
      , "to_str"
      ]

----------
-- Kind --
----------

pKind ∷ CParser TokenBasic Kind
pKind = cpNewContext "kind" $ concat
  [ do concat [cpSyntaxVoid "☆",cpSyntaxVoid "type"] ; return TypeK
  , do concat [cpSyntaxVoid "ℙ",cpSyntaxVoid "prin"] ; return PrinK
  , do concat [cpSyntaxVoid "ℙs",cpSyntaxVoid "prins"] ; return PrinsK
  ]

----------
-- Prin --
----------

pPrin ∷ CParser TokenBasic 𝕏
pPrin = cpNewContext "prin" cpName

pPrinExp ∷ CParser TokenBasic PrinExp
pPrinExp = cpNewContext "prin-exp" $ do
  concat
    [ do cpSyntaxVoid "this"
         return ThisPE
    , do ρ ← pPrin
         concat
           [ do cpSyntaxVoid "."
                concat
                  [ do cpSyntaxVoid "*"
                       return $ StarPE ρ
                  , do n ← natΩ ^$ cpInteger
                       return $ AccessPE ρ n
                  ]
           , return $ VarPE ρ
           ]
    ]

--------------
-- Prin-set --
--------------

pPrins ∷ CParser TokenBasic (𝐿 PrinExp)
pPrins = cpManySepBy (cpSyntaxVoid ",") pPrinExp

pPrinExps ∷ CParser TokenBasic (𝐿 PrinExp)
pPrinExps = cpManySepBy (cpSyntaxVoid ",") pPrinExp

----------------
-- Constraint --
----------------

pConstr ∷ CParser TokenBasic Constr
pConstr = cpNewContext "constr" $ do
  do ρs₁ ← concat
       [ do cpSyntaxVoid "{"
            ρs₁ ← pPrins
            cpSyntaxVoid "}"
            return ρs₁
       , do single ^$ pPrinExp
       ]
     concat [cpSyntaxVoid "⊆",cpSyntaxVoid "<="]
     ρs₂ ← concat
       [ do cpSyntaxVoid "{"
            ρs₂ ← pPrins
            cpSyntaxVoid "}"
            return ρs₂
       , do single ^$ pPrinExp
       ]
     return $ SubsetC ρs₁ ρs₂

------------
-- Effect --
------------

pEMode ∷ CParser TokenBasic EMode
pEMode = cpNewContext "effect-mode" $ concat
  [ do ρs ← pPrins
       return $ SecEM ρs
  , do concat [cpSyntaxVoid "⊤",cpSyntaxVoid "all"]
       return TopEM
  ]

pEffect ∷ CParser TokenBasic Effect
pEffect = cpNewContext "effect" $ do
  (ρs₁,ρs₂,em) ← concat
    [ do cpSyntaxVoid "inp"
         cpSyntaxVoid ":"
         ρs₁ ← pow ^$ pPrins
         ρs₂ ← cpOptional $ do
           cpSyntaxVoid ";"
           cpSyntaxVoid "rev"
           cpSyntaxVoid ":"
           pow ^$ pPrins
         emO ← cpOptional $ do
          cpSyntaxVoid ";"
          pEMode
         return (ρs₁,ifNone null ρs₂,ifNone TopEM emO)
    , do cpSyntaxVoid "rev"
         cpSyntaxVoid ":"
         ρs₂ ← pow ^$ pPrins
         emO ← cpOptional $ do
          cpSyntaxVoid ";"
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
  cpSyntaxVoid "#"
  concat
    [ do n₁ ← natΩ ^$ cpInteger
         n₂ ← ifNone 0 ^$ cpOptional $ do
           cpSyntaxVoid "."
           natΩ ^$ cpInteger
         return $ FixedIPr n₁ n₂
    , do concat [cpSyntaxVoid "∞",cpSyntaxVoid "inf"]
         return InfIPr
    ]

pFPrecision ∷ CParser TokenBasic FPrecision
pFPrecision = ifNone fprDefault ^$ cpOptional $ do
  cpSyntaxVoid "#"
  n₁ ← natΩ ^$ cpInteger
  cpSyntaxVoid "."
  n₂ ← natΩ ^$ cpInteger
  return $ FixedFPr n₁ n₂

----------
-- Type --
----------

pType ∷ CParser TokenBasic Type
pType = cpNewContext "type" $ mixfix $ concat
  -- α
  [ mixTerminal $ do x ← pTVar ; return $ VarT x
  -- 𝟙
  , mixTerminal $ do concat [cpSyntaxVoid "𝟙",cpSyntaxVoid "unit"] ; return UnitT
  -- 𝔹
  , mixTerminal $ do concat [cpSyntaxVoid "𝔹",cpSyntaxVoid "bool"] ; return $ BaseT 𝔹T
  -- 𝕊
  , mixTerminal $ do concat [cpSyntaxVoid "𝕊",cpSyntaxVoid "string"] ; return 𝕊T
  -- ℙ
  , mixTerminal $ do concat [cpSyntaxVoid "ℙ",cpSyntaxVoid "prin"] ; return ℙT
  -- ℙs
  , mixTerminal $ do concat [cpSyntaxVoid "ℙs",cpSyntaxVoid "prins"] ; return ℙsT
  -- ℕ#n.n
  , mixTerminal $ do
      concat [cpSyntaxVoid "ℕ",cpSyntaxVoid "nat"]
      pr ← pIPrecision
      return $ BaseT $ ℕT pr
  -- ℤ#n.n
  , mixTerminal $ do
      concat [cpSyntaxVoid "ℤ",cpSyntaxVoid "int"]
      pr ← pIPrecision
      return $ BaseT $ ℤT pr
  -- 𝔽#n
  , mixTerminal $ do
      concat [cpSyntaxVoid "𝔽",cpSyntaxVoid "flt"]
      pr ← pFPrecision
      return $ BaseT $ 𝔽T pr
  -- τ + τ
  , mixInfixL levelPLUS $ do concat [cpSyntaxVoid "+"] ; return (:+:)
  -- τ × τ
  , mixInfixL levelTIMES $ do concat [cpSyntaxVoid "×",cpSyntaxVoid "*"] ; return (:×:)
  -- list τ
  , mixPrefix levelAPP $ do cpSyntaxVoid "list" ; return ListT
  -- ref τ
  , mixPrefix levelAPP $ do cpSyntaxVoid "ref" ; return RefT
  -- arr τ
  , mixPrefix levelAPP $ do cpSyntaxVoid "array" ; return ArrT
  -- τ →{η} τ
  , mixInfixR levelARROW $ do
      concat [cpSyntaxVoid "→",cpSyntaxVoid "->"]
      ηO ← cpOptional $ do
        cpSyntaxVoid "{"
        η ← pEffect
        cpSyntaxVoid "}"
        return η
      let η₀ = Effect null null TopEM
      return $ \ τ₁ τ₂ → τ₁ :→: (ifNone η₀ ηO :* τ₂)
  -- (x : τ | c,…,c) →{η} τ
  , mixPrefix levelARROW $ do
      cpSyntaxVoid "("
      x ← pVar
      cpSyntaxVoid ":"
      τ₁ ← pType
      cs ← ifNone Nil ^$ cpOptional $ do
        cpSyntaxVoid "|"
        cpManySepBy (cpSyntaxVoid ",") pConstr
      cpSyntaxVoid ")"
      concat [cpSyntaxVoid "→",cpSyntaxVoid "->"]
      ηO ← cpOptional $ do
        cpSyntaxVoid "{"
        η ← pEffect
        cpSyntaxVoid "}"
        return η
      let η₀ = Effect null null TopEM
      return $ \ τ₂ → (x :* τ₁ :* cs) :→†: (ifNone η₀ ηO :* τ₂)
  -- ∀ α:κ,…,α:κ | c,…,c. τ
  , mixPrefix levelLAM $ do
      concat [cpSyntaxVoid "∀", cpSyntaxVoid "forall"]
      ακs ← cpManySepBy (cpSyntaxVoid ",") $ do
        α ← pTVar
        cpSyntaxVoid ":"
        κ ← pKind
        return $ α :* κ
      cs ← ifNone Nil ^$ cpOptional $ do
        cpSyntaxVoid "|"
        cpManySepBy (cpSyntaxVoid ",") pConstr
      cpSyntaxVoid "."
      return $ ForallT ακs cs
  -- τ{P}
  , mixPostfix levelMODE $ do
      cpSyntaxVoid "{"
      ρes ← pPrinExps
      cpSyntaxVoid "}"
      return $ SecT ρes
  -- τ{bundle:P}
  , mixPostfix levelMODE $ do
      cpSyntaxVoid "{"
      cpSyntaxVoid "bundle"
      cpSyntaxVoid ":"
      ρes ← pPrinExps
      cpSyntaxVoid "}"
      return $ ISecT ρes
  -- τ{φ:P}
  , mixPostfix levelMODE $ do
      cpSyntaxVoid "{"
      φ ← pProt
      cpSyntaxVoid ":"
      ρes ← pPrinExps
      cpSyntaxVoid "}"
      return $ ShareT φ ρes
  -- nizk-test{P} τ
  , mixPrefix levelAPP $ do
      cpSyntaxVoid "nizk-test"
      cpSyntaxVoid "{"
      ρs ← pPrins
      cpSyntaxVoid "}"
      return $ NizkTestT ρs
  -- nizk-verify{P} τ
  , mixPrefix levelAPP $ do
      cpSyntaxVoid "nizk-verify"
      cpSyntaxVoid "{"
      ρs ← pPrins
      cpSyntaxVoid "}"
      return $ NizkVerifyT ρs
  -- (τ)
  , mixTerminal $ do cpSyntaxVoid "(" ; τ ← pType ; cpSyntaxVoid ")" ; return τ
  ]

--------------
-- Literals --
--------------

pBool ∷ CParser TokenBasic 𝔹
pBool = concat
  [ do cpSyntaxVoid "true" ; return True
  , do cpSyntaxVoid "false" ; return False
  ]

----------
-- Prot --
----------

pProt ∷ CParser TokenBasic Prot
pProt = cpNewContext "prot" $ concat
  [ do cpSyntaxVoid "plain" ; return PlainP
  , do cpSyntaxVoid "yao"   ; return Yao2P
  , do cpSyntaxVoid "yaoN"  ; return YaoNP
  , do cpSyntaxVoid "yao2"  ; return Yao2P
  , do cpSyntaxVoid "bgw"   ; return BGWP
  , do cpSyntaxVoid "gmw"   ; return GMWP
  , do cpSyntaxVoid "bgv"   ; return BGVP
  , do cpSyntaxVoid "spdz"  ; return SPDZP
  , do cpSyntaxVoid "auto"  ; return AutoP
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
  , mixTerminal $ do concat [cpSyntaxVoid "•",cpSyntaxVoid "()"] ; return BulP
  -- L ψ
  , mixPrefix levelAPP $ do cpSyntaxVoid "L" ; return LP
  -- R ψ
  , mixPrefix levelAPP $ do cpSyntaxVoid "R" ; return RP
  -- ψ,ψ
  , mixInfixL levelCOMMA $ do cpSyntaxVoid "," ; return TupP
  -- []
  , mixTerminal $ do cpSyntaxVoid "[]" ; return NilP
  -- ψ∷ψ
  , mixInfixR levelCONS $ do concat [cpSyntaxVoid "∷",cpSyntaxVoid "::"] ; return ConsP
  -- ⟪⟫
  , mixTerminal $ do concat [cpSyntaxVoid "⟪⟫",cpSyntaxVoid "<<>>"] ; return EmptyP
  -- ⟪ρ|ψ⟫⧺ψ
  , mixPrefix levelPLUS $ do
      concat [cpSyntaxVoid "⟪",cpSyntaxVoid "<<"]
      ρ ← pPrin
      cpSyntaxVoid "|"
      ψ ← pPat
      concat [cpSyntaxVoid "⟫",cpSyntaxVoid ">>"]
      concat [cpSyntaxVoid "⧺",cpSyntaxVoid "++"]
      return $ BundleP ρ ψ
  -- {}
  , mixTerminal $ do cpSyntaxVoid "{}" ; return EmptySetP
  -- {ρ}∪ψ
  , mixPrefix levelPLUS $ do
      cpSyntaxVoid "{"
      ρ ← pPrin
      cpSyntaxVoid "}"
      concat [cpSyntaxVoid "∪",cpSyntaxVoid "\\/"]
      return $ SetP ρ
  -- ψ : τ
  , mixPostfix levelASCR $ do
      cpSyntaxVoid ":"
      τ ← pType
      return $ \ ψ → AscrP ψ τ
  -- _
  , mixTerminal $ do cpSyntaxVoid "_" ; return WildP
  -- (ψ)
  , mixTerminal $ do cpSyntaxVoid "(" ; ψ ← pPat ; cpSyntaxVoid ")" ; return ψ
  -- [ψ₁;…;ψₙ]
  , mixTerminal $ do
      cpSyntaxVoid "["
      -- ψs ← cpManySepByContext cpWithContextRendered (cpSyntaxVoid ";") pPat
      ψs ← cpManySepBy (cpSyntaxVoid ";") pPat
      cpSyntaxVoid "]"
      return $ foldrOnFrom ψs NilP $ \ ψ₁ ψ₂ → ConsP ψ₁ ψ₂
  -- ⟪ρ₁|ψ₁;…ρₙ|ψₙ⟫
  , mixTerminal $ do
      do concat [cpSyntaxVoid "⟪",cpSyntaxVoid "<<"]
         ψρs ← cpManySepBy (cpSyntaxVoid ";") $ do
           ρ ← pPrin
           cpSyntaxVoid "|"
           ψ ← pPat
           return $ ρ :* ψ
         concat [cpSyntaxVoid "⟫",cpSyntaxVoid ">>"]
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
  , fmixTerminal $ do concat [cpSyntaxVoid "•",cpSyntaxVoid "()"] ; return BulE
  -- [mux] if e then e else e
  , fmixPrefix levelIF $ do
      b ← cpOptional $ cpSyntaxVoid "mux"
      cpSyntaxVoid "if"
      e₁ ← pExp
      cpSyntaxVoid "then"
      e₂ ← pExp
      cpSyntaxVoid "else"
      return $
        if b ≡ Some ()
        then MuxIfE e₁ e₂
        else IfE e₁ e₂
  -- L e
  , fmixPrefix levelAPP $ do cpSyntaxVoid "L" ; return LE
  -- R e
  , fmixPrefix levelAPP $ do cpSyntaxVoid "R" ; return RE
  -- e,e
  , fmixInfixL levelCOMMA $ do cpSyntaxVoid "," ; return TupE
  -- []
  , fmixTerminal $ do cpSyntaxVoid "[]" ; return NilE
  -- e∷e
  , fmixInfixR levelCONS $ do concat [cpSyntaxVoid "∷",cpSyntaxVoid "::"] ; return ConsE
  -- let x : τ in e
  , fmixPrefix levelLET $ do
      cpSyntaxVoid "let"
      ψ ← pPat
      eO ← cpOptional $ do
        cpSyntaxVoid "="
        pExp
      void $ cpOptional $ cpSyntaxVoid "in"
      return $ case eO of
        None → LetTyE ψ
        Some e → LetE ψ e
  -- [mux] case e {ψ→e;…;ψ→e}
  , fmixTerminal $ do
      b ← cpOptional $ cpSyntaxVoid "mux"
      cpSyntaxVoid "case"
      e ← pExp
      cpSyntaxVoid "{"
      ψes ← cpManySepBy (cpSyntaxVoid ";") $ do
        ψ ← pPat
        concat [cpSyntaxVoid "→",cpSyntaxVoid "->"]
        e' ← pExp
        return $ ψ :* e'
      cpSyntaxVoid "}"
      return $
        if b ≡ Some ()
        then MuxCaseE e ψes
        else CaseE e ψes
  -- λ [x] ψ…ψ → e
  , fmixPrefix levelLAM $ do
      concat [cpSyntaxVoid "λ",cpSyntaxVoid "fun"]
      xO ← cpOptional $ do
        cpSyntaxVoid "["
        x ← pVar
        cpSyntaxVoid "]"
        return x
      ψs ← cpMany pPat
      concat [cpSyntaxVoid "→",cpSyntaxVoid "->"]
      return $ LamE xO ψs
  -- e e
  , fmixInfixL levelAPP $ return AppE
  -- Λ α → e
  , fmixPrefix levelLAM $ do
      concat [cpSyntaxVoid "Λ",cpSyntaxVoid "abs"]
      α ← pTVar
      concat [cpSyntaxVoid "→",cpSyntaxVoid "->"]
      return $ TLamE α
  -- e @ τ
  , fmixPostfix levelAPP $ do
      cpSyntaxVoid "@"
      τ ← pType
      return $ \ e → TAppE e τ
  -- par {P} e
  , fmixPrefix levelPAR $ do
      cpSyntaxVoid "par"
      cpSyntaxVoid "{"
      ρes ← pPrinExps
      cpSyntaxVoid "}"
      return $ ParE ρes
  -- share{φ,τ:P→P} e
  , fmixPrefix levelAPP $ do
      cpSyntaxVoid "share"
      cpSyntaxVoid "{"
      φ ← pProt
      cpSyntaxVoid ","
      τ ← pType
      cpSyntaxVoid ":"
      ρes₁ ← pPrinExps
      concat [cpSyntaxVoid "→",cpSyntaxVoid "->"]
      ρes₂ ← pPrinExps
      cpSyntaxVoid "}"
      return $ ShareE φ τ ρes₁ ρes₂
  -- e@ρ
  , fmixPostfix levelACCESS $ do cpSyntaxVoid "@" ; ρe ← pPrinExp ; return $ \ e → AccessE e ρe
  -- ⟪⟫
  , fmixTerminal $ do concat [cpSyntaxVoid "⟪⟫",cpSyntaxVoid "<<>>"] ; return $ BundleE null
  -- ⟪ρ₁|e₁;…;ρₙ|eₙ⟫
  , fmixTerminal $ do
      concat [cpSyntaxVoid "⟪",cpSyntaxVoid "<<"]
      ρes ← cpManySepBy (cpSyntaxVoid ";") $ do
        ρe ← pPrinExp
        cpSyntaxVoid "|"
        e ← pExp
        return $ ρe :* e
      concat [cpSyntaxVoid "⟫",cpSyntaxVoid ">>"]
      return $ BundleE ρes
  -- e⧺e
  , fmixInfixL levelPLUS $ do concat [cpSyntaxVoid "⧺",cpSyntaxVoid "++"] ; return BundleUnionE
  -- reveal{P→P} e
  , fmixPrefix levelREVEAL $ do
      cpSyntaxVoid "reveal"
      cpSyntaxVoid "{"
      φ ← pProt
      cpSyntaxVoid ":"
      ρes₁ ← pPrinExps
      concat [cpSyntaxVoid "→",cpSyntaxVoid "->"]
      ρes₂ ← pPrinExps
      cpSyntaxVoid "}"
      return $ RevealE φ ρes₁ ρes₂
  -- send{P→P} e
  , fmixPrefix levelAPP $ do
      cpSyntaxVoid "send"
      cpSyntaxVoid "{"
      ρes₁ ← pPrinExps
      concat [cpSyntaxVoid "→",cpSyntaxVoid "->"]
      ρes₂ ← pPrinExps
      cpSyntaxVoid "}"
      return $ SendE ρes₁ ρes₂
  -- e:τ
  , fmixPostfix levelASCR $ do
      cpSyntaxVoid ":"
      τ ← pType
      return $ \ e → AscrE e τ
  -- read τ from e
  , fmixPrefix levelAPP $ do
      cpSyntaxVoid "read"
      τ ← pType
      cpSyntaxVoid "from"
      return $ ReadE τ
  -- write e to e
  , fmixPrefix levelAPP $ do
      cpSyntaxVoid "write"
      e ← pExp
      cpSyntaxVoid "to"
      return $ WriteE e
  -- rand e
  , fmixTerminal $ do
      cpSyntaxVoid "rand"
      τ ← pType
      return $ RandE τ
  -- rand-range τ e
  , fmixPrefix levelAPP $ do
      cpSyntaxVoid "rand-range"
      τ ← pType
      return $ RandRangeE τ
  -- sign {P} e
  , fmixPrefix levelAPP $ do
      cpSyntaxVoid "sign"
      cpSyntaxVoid "{"
      ρs ← pPrinExps
      cpSyntaxVoid "}"
      return $ SignE ρs
  -- unsign {P} e
  , fmixPrefix levelAPP $ do
      cpSyntaxVoid "unsign"
      cpSyntaxVoid "{"
      ρs ← pPrinExps
      cpSyntaxVoid "}"
      return $ UnsignE ρs
  -- is-signed {P} e
  , fmixPrefix levelAPP $ do
      cpSyntaxVoid "is-signed"
      cpSyntaxVoid "{"
      ρs ← pPrinExps
      cpSyntaxVoid "}"
      return $ IsSignedE ρs
  -- _
  , fmixTerminal $ do cpSyntaxVoid "_" ; return InferE
  -- ⁇
  , fmixTerminal $ do cpSyntaxVoid "??" ; return HoleE
  -- (e)
  , fmixTerminal $ do cpSyntaxVoid "(" ; e ← pExp ; cpSyntaxVoid ")" ; return $ extract e
  -- []
  , fmixTerminal $ do cpSyntaxVoid "[]" ; return NilE
  -- [e₁;…;eₙ]
  , fmixTerminal $ do
      cpSyntaxVoid "["
      es ← cpManySepByContext cpWithContextRendered (cpSyntaxVoid ";") pExp
      a ← atag ^$ cpWithContextRendered $ cpSyntaxVoid "]"
      return $ extract $ foldrOnFrom es (𝐴 a NilE) $ \ (𝐴 a₁ e₁) e₂ → 𝐴 a₁ $ ConsE e₁ e₂
  -- {P}
  , fmixTerminal $ do
      cpSyntaxVoid "{"
      ρes ← pPrinExps
      cpSyntaxVoid "}"
      return $ SetE ρes
  -- ref e
  , fmixPrefix levelAPP $ do cpSyntaxVoid "ref" ; return RefE
  -- !e
  , fmixPrefix levelDEREF $ do cpSyntaxVoid "!" ; return RefReadE
  -- e ≔ e
  , fmixInfixR levelUPDATE $ do concat [cpSyntaxVoid "≔",cpSyntaxVoid ":="] ; return RefWriteE
  -- array[e] e
  , fmixPrefix levelAPP $ do
      cpSyntaxVoid "array"
      cpSyntaxVoid "["
      e ← pExp
      cpSyntaxVoid "]"
      return $ ArrayE e
  -- e.e
  , fmixInfix levelACCESS $ do cpSyntaxVoid "." ; return ArrayReadE
  -- e.e ← e
  , fmixInfixR levelUPDATE $ do concat [cpSyntaxVoid "←",cpSyntaxVoid "<-"] ; return ArrayWriteE
  -- size e
  , fmixPrefix levelAPP $ do cpSyntaxVoid "size" ; return SizeE
  -- ⊥
  , fmixTerminal $ do concat [cpSyntaxVoid "⊥",cpSyntaxVoid "_|_"] ; return DefaultE
  -- proc e
  , fmixPrefix levelLET $ do cpSyntaxVoid "proc" ; return ProcE
  -- return e
  , fmixPrefix levelLET $ do cpSyntaxVoid "return" ; return ReturnE
  -- nizk-witness{φ:P} e
  , fmixPrefix levelAPP $ do
      cpSyntaxVoid "nizk-witness"
      cpSyntaxVoid "{"
      φ ← pProt
      cpSyntaxVoid ":"
      ρs ← pPrins
      cpSyntaxVoid "}"
      return $ NizkWitnessE φ ρs
  -- nizk-commit{φ:P} e
  , fmixPrefix levelAPP $ do
      cpSyntaxVoid "nizk-commit"
      cpSyntaxVoid "{"
      φ ← pProt
      cpSyntaxVoid ":"
      ρs ← pPrins
      cpSyntaxVoid "}"
      return $ NizkCommitE φ ρs
  -- prim[⊙](e,…,e)
  , fmixInfixL levelPLUS $ do concat [cpSyntaxVoid "∨",cpSyntaxVoid "||"] ; return $ \ e₁ e₂ → PrimE OrO $ list [e₁,e₂]
  , fmixInfixL levelTIMES $ do concat [cpSyntaxVoid "∧",cpSyntaxVoid "&&"] ; return $ \ e₁ e₂ → PrimE AndO $ list [e₁,e₂]
  , fmixPrefix levelEXP $ do concat [cpSyntaxVoid "not",cpSyntaxVoid "¬"] ; return $ \ e → PrimE NotO $ list [e]
  , fmixInfixL levelPLUS $ do cpSyntaxVoid "+" ; return $ \ e₁ e₂ → PrimE PlusO $ list [e₁,e₂]
  , fmixInfixL levelPLUS $ do cpSyntaxVoid "-" ; return $ \ e₁ e₂ → PrimE MinusO $ list [e₁,e₂]
  , fmixInfixL levelTIMES $ do concat [cpSyntaxVoid "×",cpSyntaxVoid "*"] ; return $ \ e₁ e₂ → PrimE TimesO $ list [e₁,e₂]
  , fmixInfixL levelEXP $ do cpSyntaxVoid "^" ; return $ \ e₁ e₂ → PrimE ExpO $ list [e₁,e₂]
  , fmixInfixL levelTIMES $ do cpSyntaxVoid "/" ; return $ \ e₁ e₂ → PrimE DivO $ list [e₁,e₂]
  , fmixInfixL levelTIMES $ do cpSyntaxVoid "%" ; return $ \ e₁ e₂ → PrimE ModO $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do concat [cpSyntaxVoid "≡",cpSyntaxVoid "=="] ; return $ \ e₁ e₂ → PrimE EqO $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do cpSyntaxVoid "<" ; return $ \ e₁ e₂ → PrimE LTO $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do cpSyntaxVoid ">" ; return $ \ e₁ e₂ → PrimE GTO $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do concat [cpSyntaxVoid "≤",cpSyntaxVoid "<="] ; return $ \ e₁ e₂ → PrimE LTEO $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do concat [cpSyntaxVoid "≥",cpSyntaxVoid ">="] ; return $ \ e₁ e₂ → PrimE GTEO $ list [e₁,e₂]
  , fmixPrefix levelAPP $ do cpSyntaxVoid "abs_val" ; return $ \ e → PrimE AbsO $ list [e]
  , fmixPrefix levelAPP $ do cpSyntaxVoid "sqrt" ; return $ \ e → PrimE SqrtO $ list [e]
  , fmixPrefix levelAPP $ do cpSyntaxVoid "log_base_2" ; return $ \ e → PrimE LogO $ list [e]
  , fmixPrefix levelAPP $ do
      cpSyntaxVoid "nat"
      ip ← pIPrecision
      return $ \ e → PrimE (NatO ip) $ list [e]
  , fmixPrefix levelAPP $ do
      cpSyntaxVoid "int"
      ip ← pIPrecision
      return $ \ e → PrimE (IntO ip) $ list [e]
  , fmixPrefix levelAPP $ do
      cpSyntaxVoid "flt"
      fp ← pFPrecision
      return $ \ e → PrimE (FltO fp) $ list [e]
  , fmixPrefix levelAPP $ do
      cpSyntaxVoid "ceil"
      ip ← pIPrecision
      return $ \ e → PrimE (CeilO ip) $ list [e]
  , fmixPrefix levelAPP $ do
      cpSyntaxVoid "to_str"
      return $ \ e → ToStringE e
  , fmixInfixR levelAPP $ do
      concat [cpSyntaxVoid "⧻", cpSyntaxVoid "+++"]
      return StringConcatE
  , fmixInfixR levelCOND $ do
      cpSyntaxVoid "?"
      e₂ ← pExp
      concat [cpSyntaxVoid "◇",cpSyntaxVoid "><"]
      return $ \ e₁ e₃ → PrimE CondO $ list [e₁,e₂,e₃]
  -- trace e in e
  , fmixPrefix levelLET $ do
      cpSyntaxVoid "trace"
      e₁ ← pExp
      void $ cpOptional $ cpSyntaxVoid "in"
      return $ TraceE e₁
  -----------
  -- sugar --
  -----------
  -- solo P as x in e
  , fmixPrefix levelLET $ do
      cpSyntaxVoid "solo"
      cpSyntaxVoid "{"
      ρes ← pPrinExps
      cpSyntaxVoid "}"
      xO ← cpOptional $ do
        cpSyntaxVoid "as"
        x ← pVar
        cpSyntaxVoid "in"
        return x
      return $ \ e →
        AppE (siphon e $
              AppE (siphon e $ VarE $ var "solo-f") $
                   siphon e $ SetE ρes) $
             siphon e $
             LamE None (single $ elim𝑂 WildP VarP xO) e
  -- fold e as x . x on e as x in e
  , fmixPrefix levelLET $ do
      cpSyntaxVoid "fold"
      e₁ ← pExp
      cpSyntaxVoid "as"
      x₁ ← pVar
      cpSyntaxVoid "."
      x₂ ← pVar
      cpSyntaxVoid "on"
      e₂ ← pExp
      cpSyntaxVoid "as"
      x₃ ← pVar
      cpSyntaxVoid "in"
      return $ \ e →
        AppE (siphon e $
              AppE (siphon e $
                    AppE (siphon e $ VarE $ var "fold-f") $
                         e₂) $
                   siphon e $ LamE None (list [VarP x₁,VarP x₂,VarP x₃]) e) $
             e₁
  -- do e in e
  , fmixPrefix levelLET $ do
      cpSyntaxVoid "do"
      e ← pExp
      void $ cpOptional $ cpSyntaxVoid "in"
      return $ LetE (VarP $ var "") e
  -- loop e in e
  , fmixPrefix levelLET $ do
      cpSyntaxVoid "loop"
      e₁ ← pExp
      cpSyntaxVoid "in"
      return $ \ e₂ →
        AppE (siphon e₁ $
              AppE (siphon e₁ $ VarE $ var "loop-f")
                   (siphon e₁ $ LamE None (list [WildP]) e₂))
             e₁
  -- [mux] when e then e
  , fmixPrefix levelLET $ do
      b ← cpOptional $ cpSyntaxVoid "mux"
      cpSyntaxVoid "when"
      e₁ ← pExp
      cpSyntaxVoid "then"
      return $ \ e₂ →
        if b ≡ Some ()
        then MuxIfE e₁ e₂ $ siphon e₁ DefaultE
        else IfE e₁ e₂ $ siphon e₁ DefaultE
  ]

---------------
-- Top-level --
---------------

pTL ∷ CParser TokenBasic TL
pTL = cpNewWithContextRendered "tl" $ concat
  [ do cpSyntaxVoid "def"
       b ← ifNone False ^$ cpOptional $ do
         cpSyntaxVoid "sec"
         return True
       x ← pVar
       ψs ← cpMany pPat
       concat
         [ do cpSyntaxVoid ":"
              τ ← pType
              return $ DeclTL b x τ
         , do cpSyntaxVoid "="
              e ← pExp
              return $ DefnTL b x ψs e
         ]
  , do cpSyntaxVoid "principal"
       ρds ← cpOneOrMore $ do
         ρ ← 𝕩name ^$ pPrin
         nO ← cpOptional $ do
           cpSyntaxVoid "["
           n ← natΩ ^$ cpInteger
           cpSyntaxVoid "]"
           return n
         return $ case nO of
           None → SinglePD ρ
           Some n → ArrayPD ρ n
       return $ PrinTL ρds
  , do cpSyntaxVoid "primitive"
       x ← pVar
       cpSyntaxVoid ":"
       τ ← pType
       return $ PrimTL x τ
  , do cpSyntaxVoid "import"
       s ← cpString
       xρs ← ifNone Nil ^$ cpOptional $ do
         cpSyntaxVoid "with"
         cpOneOrMore $ do
           x ← 𝕩name ^$ pVar
           cpSyntaxVoid "="
           cpSyntaxVoid "{"
           ρs ← pPrinExps
           cpSyntaxVoid "}"
           return $ x :* ρs
       return $ ImportTL s xρs
  , do cpSyntaxVoid "virtual"
       cpSyntaxVoid "party"
       xs ← 𝕩name ^^$ cpOneOrMore pVar
       return $ VirtualPartyTL xs
  ]

cpTLs ∷ CParser TokenBasic (𝐿 TL)
cpTLs = cpMany pTL

testParserExample ∷ 𝕊 → IO ()
testParserExample fn = do
  let path = "examples/" ⧺ fn ⧺ ".psl"
  s ← fread fn
  let ts = tokens s
  ls ← tokenizeIO lexer path ts
  _tls ← parseIO cpTLs path ls
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
