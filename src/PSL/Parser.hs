module PSL.Parser where

import UVMHS
-- import AddToUVMHS

import PSL.Syntax
import PSL.Interpreter.Pretty

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
      [ "yaoN","yao2","gmw","bgw","bgv","spdz","auto"
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
  concat
    [ do cpSyntax "this"
         return ThisPE
    , do ρ ← pPrin
         concat
           [ do cpSyntax "."
                concat
                  [ do cpSyntax "*"
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
  [ do ρs ← pPrins
       return $ SecEM ρs
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
  n₁ ← natΩ ^$ cpInteger
  cpSyntax "."
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
  , mixTerminal $ do concat [cpSyntax "𝟙",cpSyntax "unit"] ; return UnitT
  -- 𝔹
  , mixTerminal $ do concat [cpSyntax "𝔹",cpSyntax "bool"] ; return $ BaseT 𝔹T
  -- 𝕊
  , mixTerminal $ do concat [cpSyntax "𝕊",cpSyntax "string"] ; return 𝕊T
  -- ℙ
  , mixTerminal $ do concat [cpSyntax "ℙ",cpSyntax "prin"] ; return ℙT
  -- ℙs
  , mixTerminal $ do concat [cpSyntax "ℙs",cpSyntax "prins"] ; return ℙsT
  -- ℕ#n.n
  , mixTerminal $ do
      concat [cpSyntax "ℕ",cpSyntax "nat"]
      pr ← pIPrecision
      return $ BaseT $ ℕT pr
  -- ℤ#n.n
  , mixTerminal $ do
      concat [cpSyntax "ℤ",cpSyntax "int"]
      pr ← pIPrecision
      return $ BaseT $ ℤT pr
  -- 𝔽#n
  , mixTerminal $ do
      concat [cpSyntax "𝔽",cpSyntax "flt"]
      pr ← pFPrecision
      return $ BaseT $ 𝔽T pr
  -- τ + τ
  , mixInfixL levelPLUS $ do concat [cpSyntax "+"] ; return (:+:)
  -- τ × τ
  , mixInfixL levelTIMES $ do concat [cpSyntax "×",cpSyntax "*"] ; return (:×:)
  -- list τ
  , mixPrefix levelAPP $ do cpSyntax "list" ; return ListT
  -- ref τ
  , mixPrefix levelAPP $ do cpSyntax "ref" ; return RefT
  -- arr τ
  , mixPrefix levelAPP $ do cpSyntax "array" ; return ArrT
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
  -- ∀ α:κ,…,α:κ | c,…,c. τ
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
  -- τ{P}
  , mixPostfix levelMODE $ do
      cpSyntax "{"
      ρes ← pPrinExps
      cpSyntax "}"
      return $ SecT ρes
  -- τ{bundle:P}
  , mixPostfix levelMODE $ do
      cpSyntax "{"
      cpSyntax "bundle"
      cpSyntax ":"
      ρes ← pPrinExps
      cpSyntax "}"
      return $ ISecT ρes
  -- τ{φ:P}
  , mixPostfix levelMODE $ do
      cpSyntax "{"
      φ ← pProt
      cpSyntax ":"
      ρes ← pPrinExps
      cpSyntax "}"
      return $ ShareT φ ρes
  -- nizk-test{P} τ
  , mixPrefix levelAPP $ do
      cpSyntax "nizk-test"
      cpSyntax "{"
      ρs ← pPrins
      cpSyntax "}"
      return $ NizkTestT ρs
  -- nizk-verify{P} τ
  , mixPrefix levelAPP $ do
      cpSyntax "nizk-verify"
      cpSyntax "{"
      ρs ← pPrins
      cpSyntax "}"
      return $ NizkVerifyT ρs
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
  [ do cpSyntax "yaoN" ; return YaoN_P
  , do cpSyntax "yao2" ; return Yao2_P
  , do cpSyntax "bgw"  ; return BGWP
  , do cpSyntax "gmw"  ; return GMWP
  , do cpSyntax "bgv"  ; return BGVP
  , do cpSyntax "spdz" ; return SPDZP
  , do cpSyntax "auto" ; return AutoP
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
  -- ⟪ρ|ψ⟫⧺ψ
  , mixPrefix levelPLUS $ do
      concat [cpSyntax "⟪",cpSyntax "<<"]
      ρ ← pPrin
      cpSyntax "|"
      ψ ← pPat
      concat [cpSyntax "⟫",cpSyntax ">>"]
      concat [cpSyntax "⧺",cpSyntax "++"]
      return $ BundleP ρ ψ
  -- {}
  , mixTerminal $ do cpSyntax "{}" ; return EmptySetP
  -- {ρ}∪ψ
  , mixPrefix levelPLUS $ do
      cpSyntax "{"
      ρ ← pPrin
      cpSyntax "}"
      concat [cpSyntax "∪",cpSyntax "\\/"]
      return $ SetP ρ
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
  -- ⟪ρ₁|ψ₁;…ρₙ|ψₙ⟫
  , mixTerminal $ do
      do concat [cpSyntax "⟪",cpSyntax "<<"]
         ψρs ← cpManySepBy (cpSyntax ";") $ do
           ρ ← pPrin
           cpSyntax "|"
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
  -- [mux] if e then e else e
  , fmixPrefix levelIF $ do
      b ← cpOptional $ cpSyntax "mux"
      cpSyntax "if"
      e₁ ← pExp
      cpSyntax "then"
      e₂ ← pExp
      cpSyntax "else"
      return $
        if b ≡ Some ()
        then MuxIfE e₁ e₂
        else IfE e₁ e₂
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
  -- let x : τ in e
  , fmixPrefix levelLET $ do
      cpSyntax "let"
      ψ ← pPat
      eO ← cpOptional $ do
        cpSyntax "="
        pExp
      void $ cpOptional $ cpSyntax "in"
      return $ case eO of
        None → LetTyE ψ
        Some e → LetE ψ e
  -- [mux] case e {ψ→e;…;ψ→e}
  , fmixTerminal $ do
      b ← cpOptional $ cpSyntax "mux"
      cpSyntax "case"
      e ← pExp
      cpSyntax "{"
      ψes ← cpManySepBy (cpSyntax ";") $ do
        ψ ← pPat
        concat [cpSyntax "→",cpSyntax "->"]
        e' ← pExp
        return $ ψ :* e'
      cpSyntax "}"
      return $
        if b ≡ Some ()
        then MuxCaseE e ψes
        else CaseE e ψes
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
  -- par {P[:τ]} e
  , fmixPrefix levelPAR $ do
      cpSyntax "par"
      cpSyntax "{"
      ρes ← pPrinExps
      oτ ← cpOptional $ do
        cpSyntax ":"
        pType
      cpSyntax "}"
      return $ ParE ρes oτ
  -- share{φ:P→P} e
  , fmixPrefix levelAPP $ do
      cpSyntax "share"
      cpSyntax "{"
      φ ← pProt
      cpSyntax ":"
      ρes₁ ← pPrinExps
      concat [cpSyntax "→",cpSyntax "->"]
      ρes₂ ← pPrinExps
      cpSyntax "}"
      return $ ShareE φ ρes₁ ρes₂
  -- e@ρ
  , fmixPostfix levelACCESS $ do cpSyntax "@" ; ρe ← pPrinExp ; return $ \ e → AccessE e ρe
  -- ⟪⟫
  , fmixTerminal $ do concat [cpSyntax "⟪⟫",cpSyntax "<<>>"] ; return $ BundleE null
  -- ⟪ρ₁|e₁;…;ρₙ|eₙ⟫
  , fmixTerminal $ do
      concat [cpSyntax "⟪",cpSyntax "<<"]
      ρes ← cpManySepBy (cpSyntax ";") $ do
        ρe ← pPrinExp
        cpSyntax "|"
        e ← pExp
        return $ ρe :* e
      concat [cpSyntax "⟫",cpSyntax ">>"]
      return $ BundleE ρes
  -- e⧺e
  , fmixInfixL levelPLUS $ do concat [cpSyntax "⧺",cpSyntax "++"] ; return BundleUnionE
  -- reveal{P→P} e
  , fmixPrefix levelAPP $ do
      cpSyntax "reveal"
      cpSyntax "{"
      φ ← pProt
      cpSyntax ":"
      ρes₁ ← pPrinExps
      concat [cpSyntax "→",cpSyntax "->"]
      ρes₂ ← pPrinExps
      cpSyntax "}"
      return $ RevealE φ ρes₁ ρes₂
  -- send{P→P} e
  , fmixPrefix levelAPP $ do
      cpSyntax "send"
      cpSyntax "{"
      ρes₁ ← pPrinExps
      concat [cpSyntax "→",cpSyntax "->"]
      ρes₂ ← pPrinExps
      cpSyntax "}"
      return $ SendE ρes₁ ρes₂
  -- e:τ
  , fmixPostfix levelASCR $ do
      cpSyntax ":"
      τ ← pType
      return $ \ e → AscrE e τ
  -- read τ from e
  , fmixPrefix levelAPP $ do
      cpSyntax "read"
      τ ← pType
      cpSyntax "from"
      return $ ReadE τ
  -- write e to e
  , fmixPrefix levelAPP $ do
      cpSyntax "write"
      e ← pExp
      cpSyntax "to"
      return $ WriteE e
  -- rand e
  , fmixTerminal $ do
      cpSyntax "rand"
      τ ← pType
      return $ RandE τ
  -- rand-range τ e
  , fmixPrefix levelAPP $ do
      cpSyntax "rand-range"
      τ ← pType
      return $ RandRangeE τ
  -- sign {P} e
  , fmixPrefix levelAPP $ do
      cpSyntax "sign"
      cpSyntax "{"
      ρs ← pPrinExps
      cpSyntax "}"
      return $ SignE ρs
  -- unsign {P} e
  , fmixPrefix levelAPP $ do
      cpSyntax "unsign"
      cpSyntax "{"
      ρs ← pPrinExps
      cpSyntax "}"
      return $ UnsignE ρs
  -- is-signed {P} e
  , fmixPrefix levelAPP $ do
      cpSyntax "is-signed"
      cpSyntax "{"
      ρs ← pPrinExps
      cpSyntax "}"
      return $ IsSignedE ρs
  -- _
  , fmixTerminal $ do cpSyntax "_" ; return InferE
  -- ⁇
  , fmixTerminal $ do cpSyntax "??" ; return HoleE
  -- (e)
  , fmixTerminal $ do cpSyntax "(" ; e ← pExp ; cpSyntax ")" ; return $ extract e
  -- []
  , fmixTerminal $ do cpSyntax "[]" ; return NilE
  -- [e₁;…;eₙ]
  , fmixTerminal $ do
      cpSyntax "["
      es ← cpManySepByContext cpWithContextRendered (cpSyntax ";") pExp
      a ← annotatedTag ^$ cpWithContextRendered $ cpSyntax "]"
      return $ extract $ foldrOnFrom es (Annotated a NilE) $ \ (Annotated a₁ e₁) e₂ → Annotated a₁ $ ConsE e₁ e₂
  -- {P}
  , fmixTerminal $ do
      cpSyntax "{"
      ρes ← pPrinExps
      cpSyntax "}"
      return $ SetE ρes
  -- ref e
  , fmixPrefix levelAPP $ do cpSyntax "ref" ; return RefE
  -- !e
  , fmixPrefix levelDEREF $ do cpSyntax "!" ; return RefReadE
  -- e ≔ e
  , fmixInfixR levelUPDATE $ do concat [cpSyntax "≔",cpSyntax ":="] ; return RefWriteE
  -- array[e] e
  , fmixPrefix levelAPP $ do
      cpSyntax "array"
      cpSyntax "["
      e ← pExp
      cpSyntax "]"
      return $ ArrayE e
  -- e.e
  , fmixInfix levelACCESS $ do cpSyntax "." ; return ArrayReadE
  -- e.e ← e
  , fmixInfixR levelUPDATE $ do concat [cpSyntax "←",cpSyntax "<-"] ; return ArrayWriteE
  -- size e
  , fmixPrefix levelAPP $ do cpSyntax "size" ; return SizeE
  -- ⊥
  , fmixTerminal $ do concat [cpSyntax "⊥",cpSyntax "_|_"] ; return DefaultE
  -- proc e
  , fmixPrefix levelLET $ do cpSyntax "proc" ; return ProcE
  -- return e
  , fmixPrefix levelLET $ do cpSyntax "return" ; return ReturnE
  -- nizk-witness{φ:P} e
  , fmixPrefix levelAPP $ do
      cpSyntax "nizk-witness"
      cpSyntax "{"
      φ ← pProt
      cpSyntax ":"
      ρs ← pPrins
      cpSyntax "}"
      return $ NizkWitnessE φ ρs
  -- nizk-commit{φ:P} e
  , fmixPrefix levelAPP $ do
      cpSyntax "nizk-commit"
      cpSyntax "{"
      φ ← pProt
      cpSyntax ":"
      ρs ← pPrins
      cpSyntax "}"
      return $ NizkCommitE φ ρs
  -- prim[⊙](e,…,e)
  , fmixInfixL levelPLUS $ do concat [cpSyntax "∨",cpSyntax "||"] ; return $ \ e₁ e₂ → PrimE OrO $ list [e₁,e₂]
  , fmixInfixL levelTIMES $ do concat [cpSyntax "∧",cpSyntax "&&"] ; return $ \ e₁ e₂ → PrimE AndO $ list [e₁,e₂]
  , fmixPrefix levelEXP $ do concat [cpSyntax "not",cpSyntax "¬"] ; return $ \ e → PrimE NotO $ list [e]
  , fmixInfixL levelPLUS $ do cpSyntax "+" ; return $ \ e₁ e₂ → PrimE PlusO $ list [e₁,e₂]
  , fmixInfixL levelPLUS $ do cpSyntax "-" ; return $ \ e₁ e₂ → PrimE MinusO $ list [e₁,e₂]
  , fmixInfixL levelTIMES $ do concat [cpSyntax "×",cpSyntax "*"] ; return $ \ e₁ e₂ → PrimE TimesO $ list [e₁,e₂]
  , fmixInfixL levelEXP $ do cpSyntax "^" ; return $ \ e₁ e₂ → PrimE ExpO $ list [e₁,e₂]
  , fmixInfixL levelTIMES $ do cpSyntax "/" ; return $ \ e₁ e₂ → PrimE DivO $ list [e₁,e₂]
  , fmixInfixL levelTIMES $ do cpSyntax "%" ; return $ \ e₁ e₂ → PrimE ModO $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do concat [cpSyntax "≡",cpSyntax "=="] ; return $ \ e₁ e₂ → PrimE EqO $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do cpSyntax "<" ; return $ \ e₁ e₂ → PrimE LTO $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do cpSyntax ">" ; return $ \ e₁ e₂ → PrimE GTO $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do concat [cpSyntax "≤",cpSyntax "<="] ; return $ \ e₁ e₂ → PrimE LTEO $ list [e₁,e₂]
  , fmixInfix levelCOMPARE $ do concat [cpSyntax "≥",cpSyntax ">="] ; return $ \ e₁ e₂ → PrimE GTEO $ list [e₁,e₂]
  , fmixPrefix levelAPP $ do cpSyntax "abs_val" ; return $ \ e → PrimE AbsO $ list [e]
  , fmixPrefix levelAPP $ do cpSyntax "sqrt" ; return $ \ e → PrimE SqrtO $ list [e]
  , fmixPrefix levelAPP $ do cpSyntax "log_base_2" ; return $ \ e → PrimE LogO $ list [e]
  , fmixPrefix levelAPP $ do
      cpSyntax "nat"
      ip ← pIPrecision
      return $ \ e → PrimE (NatO ip) $ list [e]
  , fmixPrefix levelAPP $ do
      cpSyntax "int"
      ip ← pIPrecision
      return $ \ e → PrimE (IntO ip) $ list [e]
  , fmixPrefix levelAPP $ do
      cpSyntax "flt"
      fp ← pFPrecision
      return $ \ e → PrimE (FltO fp) $ list [e]
  , fmixPrefix levelAPP $ do
      cpSyntax "ceil"
      ip ← pIPrecision
      return $ \ e → PrimE (CeilO ip) $ list [e]
  , fmixPrefix levelAPP $ do
      cpSyntax "to_str"
      return $ \ e → ToStringE e
  , fmixInfixR levelAPP $ do
      concat [cpSyntax "⧻", cpSyntax "+++"]
      return StringConcatE
  , fmixInfixR levelCOND $ do
      cpSyntax "?"
      e₂ ← pExp
      concat [cpSyntax "◇",cpSyntax "><"]
      return $ \ e₁ e₃ → PrimE CondO $ list [e₁,e₂,e₃]
  -- trace e in e
  , fmixPrefix levelLET $ do
      cpSyntax "trace"
      e₁ ← pExp
      void $ cpOptional $ cpSyntax "in"
      return $ TraceE e₁
  -----------
  -- sugar --
  -----------
  -- solo P as x in e
  , fmixPrefix levelLET $ do
      cpSyntax "solo"
      cpSyntax "{"
      ρes ← pPrinExps
      cpSyntax "}"
      xO ← cpOptional $ do
        cpSyntax "as"
        x ← pVar
        cpSyntax "in"
        return x
      return $ \ e →
        AppE (siphon e $
              AppE (siphon e $ VarE $ var "solo-f") $
                   siphon e $ SetE ρes) $
             siphon e $
             LamE None (single $ elim𝑂 WildP VarP xO) e
  -- fold e as x . x on e as x in e
  , fmixPrefix levelLET $ do
      cpSyntax "fold"
      e₁ ← pExp
      cpSyntax "as"
      x₁ ← pVar
      cpSyntax "."
      x₂ ← pVar
      cpSyntax "on"
      e₂ ← pExp
      cpSyntax "as"
      x₃ ← pVar
      cpSyntax "in"
      return $ \ e →
        AppE (siphon e $
              AppE (siphon e $
                    AppE (siphon e $ VarE $ var "fold-f") $
                         e₂) $
                   siphon e $ LamE None (list [VarP x₁,VarP x₂,VarP x₃]) e) $
             e₁
  -- do e in e
  , fmixPrefix levelLET $ do
      cpSyntax "do"
      e ← pExp
      void $ cpOptional $ cpSyntax "in"
      return $ LetE (VarP $ var "") e
  -- loop e in e
  , fmixPrefix levelLET $ do
      cpSyntax "loop"
      e₁ ← pExp
      cpSyntax "in"
      return $ \ e₂ →
        AppE (siphon e₁ $
              AppE (siphon e₁ $ VarE $ var "loop-f")
                   (siphon e₁ $ LamE None (list [WildP]) e₂))
             e₁
  -- [mux] when e then e
  , fmixPrefix levelLET $ do
      b ← cpOptional $ cpSyntax "mux"
      cpSyntax "when"
      e₁ ← pExp
      cpSyntax "then"
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
  [ do cpSyntax "def"
       b ← ifNone False ^$ cpOptional $ do
         cpSyntax "sec"
         return True
       x ← pVar
       ψs ← cpMany pPat
       concat
         [ do cpSyntax ":"
              τ ← pType
              return $ DeclTL b x τ
         , do cpSyntax "="
              e ← pExp
              return $ DefnTL b x ψs e
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
  , do cpSyntax "import"
       s ← cpString
       xρs ← ifNone Nil ^$ cpOptional $ do
         cpSyntax "with"
         cpOneOrMore $ do
           x ← 𝕩name ^$ pVar
           cpSyntax "="
           cpSyntax "{"
           ρs ← pPrinExps
           cpSyntax "}"
           return $ x :* ρs
       return $ ImportTL s xρs
  , do cpSyntax "virtual"
       cpSyntax "party"
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
