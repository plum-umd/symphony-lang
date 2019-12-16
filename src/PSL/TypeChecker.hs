module PSL.TypeChecker where

import UVMHS

import PSL.Syntax
import PSL.Parser

import PSL.Data.Mode

----------------------
-- TYPE ENVIRONMENT --
----------------------

-- Γ ∈ ctmenv
type CTyEnv = TVar ⇰ Kind
type CTmDec = Var ⇰ Type
type CTmEnv = Var ⇰ Type
type CTLTmEnv = Var ⇰ Exp ∧ Type
type CTLDefns = Var ⇰ Exp

-----------
-- STATE --
-----------

-- Σ ∈ ctlstate
data CTLState = CTLState
  { ctlStatePrins ∷ 𝑃 𝕏
  , ctlStateTyDec ∷ CTyEnv
  , ctlStateTyEnv ∷ CTyEnv
  , ctlStateTmDec ∷ CTmDec
  , ctlStateTmEnv ∷ CTLTmEnv
  , ctlStateDefns ∷ CTLDefns
  } deriving (Eq,Ord,Show)
makePrettySum ''CTLState
makeLenses ''CTLState

σtl₀ ∷ CTLState
σtl₀ = CTLState pø dø dø dø dø dø

-------------
-- CONTEXT --
-------------

-- Ξ ∈ ccxt
data CCxt = CCxt
  { cCxtSource ∷ 𝑂 FullContext
  , cCxtPrins ∷ 𝑃 𝕏
  , cCxtTyDec ∷ CTyEnv
  , cCxtTyEnv ∷ CTyEnv
  , cCxtTmDec ∷ CTmDec
  , cCxtTmEnv ∷ CTmEnv
  , cCxtMode ∷ Mode
  }
makeLenses ''CCxt

ξ₀ ∷ CCxt
ξ₀ = CCxt None pø dø dø dø dø TopM

------------
-- OUTPUT --
------------

-- o ∈ cout
data COut = COut
  { cOutEff ∷ Effect
  } deriving (Eq,Ord,Show)
makePrettySum ''COut
makeLenses ''COut

instance Null COut where null = COut null
instance Append COut where
  COut η₁ ⧺ COut η₂ = COut $ η₁ ⧺ η₂
instance Monoid COut

-----------
-- ERROR --
-----------

data ErrorClass = 
    SyntaxError 
  | TypeError 
  | NotImplementedError 
  | InternalError
  deriving (Eq,Ord,Show)
makePrettySum ''ErrorClass

-- r ∈ cerr
data CError = CError
  { cErrorSource ∷ 𝑂 FullContext
  , cErrorClass ∷ ErrorClass
  , cErrorMsg ∷ Doc
  }

throwCErrorCxt ∷ (Monad m,MonadReader CCxt m,MonadError CError m) ⇒ ErrorClass → 𝕊 → 𝐿 (𝕊 ∧ Doc) → m a
throwCErrorCxt ec em vals = do
  es ← askL cCxtSourceL
  throwCError es ec em vals
  
throwCError ∷ (Monad m,MonadError CError m) ⇒ 𝑂 FullContext → ErrorClass → 𝕊 → 𝐿 (𝕊 ∧ Doc) → m a
throwCError es ec em vals =
  throw $ CError es ec $ ppVertical
    [ ppString em
    , ppVertical $ mapOn vals $ \ (n :* v) → ppHorizontal [ppString n,ppString "=",v]
    ]

--------------
-- TL MONAD --
--------------

newtype CTLM a = CTLM { unCTLM ∷ RWST () () CTLState (ErrorT CError ID) a }
  deriving
  (Functor
  ,Return,Bind,Monad
  ,MonadReader ()
  ,MonadWriter ()
  ,MonadState CTLState
  ,MonadError CError
  )
makePrettySum ''CTLM

mkCTLM ∷ (CTLState → CError ∨ (CTLState ∧ a)) → CTLM a
mkCTLM f = CTLM $ mkRWST $ \ () σ → ErrorT $ ID $ case f σ of
  Inl r → Inl r
  Inr (σ' :* x) → Inr (σ' :* () :* x)

runCTLM ∷ CTLState → CTLM a → CError ∨ (CTLState ∧ a)
runCTLM σ xM = case unID $ unErrorT $ runRWST () σ $ unCTLM xM of
  Inl r → Inl r
  Inr (σ' :* () :* x) → Inr $ σ' :* x

evalCTLM ∷ CTLState → CTLM a → CError ∨ a
evalCTLM σ = map snd ∘ runCTLM σ

evalCTLMIO ∷ CTLState → CTLM a → IO a
evalCTLMIO σ xM = case evalCTLM σ xM of
  Inl (CError rsO rc rm) → do
    pprint $ ppVertical
      [ ppHeader $ show𝕊 rc
      , elim𝑂 null pretty rsO
      , rm
      ]
    abortIO
  Inr x → return x

-----------
-- MONAD --
-----------

newtype CM a = CM { unCM ∷ RWST CCxt COut () (ErrorT CError ID) a }
  deriving
  (Functor
  ,Return,Bind,Monad
  ,MonadReader CCxt
  ,MonadWriter COut
  ,MonadState ()
  ,MonadError CError
  )
makePrettySum ''CM

mkCM ∷ (CCxt → CError ∨ (COut ∧ a)) → CM a
mkCM f = CM $ mkRWST $ \ γ () → ErrorT $ ID $ case f γ of
  Inl r → Inl r
  Inr (o :* x) → Inr (() :* o :* x)

runCM ∷ CCxt → CM a → CError ∨ (COut ∧ a)
runCM γ xM = case unID $ unErrorT $ runRWST γ () $ unCM xM of
  Inl r → Inl r
  Inr (() :* o :* x) → Inr (o :* x)

asCTLM ∷ CM a → CTLM (COut ∧ a)
asCTLM xM = mkCTLM $ \ σ → 
  let ξ = ξ₀ { cCxtPrins = ctlStatePrins σ
             , cCxtTyDec = ctlStateTyDec σ
             , cCxtTyEnv = ctlStateTyEnv σ
             , cCxtTmDec = ctlStateTmDec σ
             , cCxtTmEnv = map snd $ ctlStateTmEnv σ
             }
  in case runCM ξ xM of
    Inl r → Inl r 
    Inr (o :* x) → Inr $ σ :* (o :* x)

-----------------
-- TYPECHECKER --
-----------------


primInferRaw ∷ 𝕊 → 𝐿 Type → CM Type
primInferRaw o τs = case (o,tohs τs) of
  ("LTE",[ℤT n₁,ℤT n₂]) | n₁ ≡ n₂ → return 𝔹T
  ("LTE",[ℕT n₁,ℕT n₂]) | n₁ ≡ n₂ → return 𝔹T
  _ → throwCErrorCxt NotImplementedError "primInferRaw" null

primInferShare ∷ 𝕊 → 𝐿 Type → Prot → 𝑃 Prin → 𝐼 Type → CM Type
primInferShare o τs φ ρs τsA = case τs of
  Nil → do
    τ ← primInferRaw o $ list τsA
    return $ ShareT φ ρs τ
  ShareT φ' ρs' τ' :& τs' | (φ' ≡ φ) ⩓ (ρs ≡ ρs') → primInferShare o τs' φ ρs $ τsA ⧺ single τ'
  _ → throwCErrorCxt TypeError "primInferShare: τs ∉ {Nil,ShareT _ _ :& _ | φ' ≡ φ ∧ ρs' ≡ ρs}" $ frhs
    [ ("τs",pretty τs)
    ]

primInfer ∷ 𝕊 → 𝐿 Type → CM Type
primInfer o τs = case τs of
  ShareT φ ρs _ :& _ → primInferShare o τs φ ρs null
  _ → primInferRaw o τs

bindVar ∷ Var → Type → CM a → CM a
bindVar x τ = mapEnvL cCxtTmEnvL ((x ↦ τ) ⩌)

bindPat ∷ Pat → Type → CM a → CM a
bindPat ψ τ = case ψ of
  BulP → id
  VarP x → bindVar x τ
  _ → const $ throwCErrorCxt NotImplementedError "bindPat" null

elabExpInfer ∷ Exp → CM (Exp ∧ Type)
elabExpInfer e = 
  mapFst (siphon e) 
  ^$ localL cCxtSourceL (Some $ annotatedTag e) 
   $ case extract e of
       StrE s → return $ StrE s :* 𝕊T
       BulE → return $ BulE :* UnitT
       VarE x → do
         γ ← askL cCxtTmEnvL
         case γ ⋕? x of
           Some τ → return $ VarE x :* τ
           None → throwCErrorCxt SyntaxError "elabExpInfer: VarE: x ∉ γ" $ frhs
             [ ("x",pretty x)
             , ("γ",pretty γ)
             ]
       ShareE φ ρs e' → do
         eᴱ' :* τ' ← elabExpInfer e'
         τ'' ← case τ' of
               SecT _ τ'³ → return τ'³
               𝔹T → return 𝔹T
               ℕT n → return $ ℕT n
               ℤT n → return $ ℤT n
               _ → throwCErrorCxt TypeError "elabExpInfer: ShareE: τ' ∉ {SecT _ _,𝔹T,ℕT _,ℤT _}" $ frhs 
                 [ ("τ'",pretty τ')
                 ]
         return $ ShareE φ ρs eᴱ' :* ShareT φ (pow ρs) τ''
       AccessE e' ρ → do
         eᴱ' :* τ' ← elabExpInfer e'
         τ'' ← case τ' of
           ISecT ρs τ'³ →
             if ρ ∈ ρs 
             then return $ SecT ρ τ'³
             else throwCErrorCxt TypeError "elabExpInfer: AccessE: ISecT: ρ ∉ ρs" $ frhs
               [ ("ρ",pretty ρ)
               , ("ρs",pretty ρs)
               ]
           _ → throwCErrorCxt TypeError "elabExpInfer: AccessE: τ' ≠ ISecT _ _" $ frhs
             [ ("τ'",pretty τ')
             ]
         return $ AccessE eᴱ' ρ :* τ''
       PrimE o es' → do
         eτsᴱ' ← mapM elabExpInfer es'
         τ' ← primInfer o $ map snd eτsᴱ'
         return $ PrimE o (map fst eτsᴱ') :* τ'
       ParE ρs e' → do
         eᴱ' :* τ' ← elabExpInfer e'
         return $ ParE ρs eᴱ' :* ISecT (pow ρs) τ'
       ReadE τ e' → do
         case τ of
           ℕT _ → skip
           ℤT _ → skip
           _ → throwCErrorCxt TypeError "elabExpInfer: ReadE: τ ∉ {ℕT _,ℤT _}" $ frhs
             [ ("τ",pretty τ)
             ]
         eᴱ' ← elabExpCheck 𝕊T e'
         return $ ReadE τ eᴱ' :* τ
       AppE e₁ e₂ → do
         eᴱ₁ :* τ₁ ← elabExpInfer e₁
         case τ₁ of
           τ₁₁ :→: (η :* τ₁₂) → do
             eᴱ₂ ← elabExpCheck τ₁₁ e₂
             tellL cOutEffL η
             return $ AppE eᴱ₁ eᴱ₂ :* τ₁₂
           _ → throwCErrorCxt TypeError "elabExpInfer: AppE: τ₁ ≠ (_ :→: (_ :* _))" $ frhs
             [ ("τ₁",pretty τ₁)
             ]
       RevealE ρs e' → do
         eᴱ' :* τ' ← elabExpInfer e'
         case τ' of
           ShareT _ _ τ'' → return $ RevealE ρs eᴱ' :* SSecT (pow ρs) τ''
           _ → throwCErrorCxt TypeError "elabExpIner: RevealE: τ' ≠ ShareT _ _ _" $ frhs
             [ ("τ'",pretty τ')
             ]
       TupE e₁ e₂ → do
         eᴱ₁ :* τ₁ ← elabExpInfer e₁
         eᴱ₂ :* τ₂ ← elabExpInfer e₂
         return $ TupE eᴱ₁ eᴱ₂ :* (τ₁ :×: τ₂)
       _ → throwCErrorCxt NotImplementedError "elabExpInfer" null

elabExpCheck ∷ Type → Exp → CM Exp 
elabExpCheck τ e = siphon e ^$ localL cCxtSourceL (Some $ annotatedTag e) $ case extract e of
  LamE selfO ψ e' → do
    case τ of
      τ₁ :→: (η :* τ₂) → 
        let f = case selfO of
              Some self → bindVar self τ
              None → id
        in f $ do
          η' :* eᴱ ← hijackL cOutEffL $ bindPat ψ τ₁ $ elabExpCheck τ₂ e'
          when (not $ η' ⊑ η) $ \ _ → 
            throwCErrorCxt TypeError "elabExpCheck: LamE: ¬ (η' ⊑ η)" $ frhs
              [ ("η'",pretty η')
              , ("η",pretty η)
              ]
          return $ LamE selfO ψ eᴱ
      _ → throwCErrorCxt TypeError "elabExpCheck: LamE: τ ≢ (_ → _)" $ frhs
        [ ("τ",pretty τ)
        ]
  LetTyE x τ' e' → do
    eᴱ' ← mapEnvL cCxtTmDecL ((x ↦ τ') ⩌) $ elabExpCheck τ e'
    return $ LetTyE x τ' eᴱ'
  LetE ψ e₁ e₂ → do
    τ'O :* f ← case ψ of
      VarP x → do
        xτs ← askL cCxtTmDecL
        return $ (xτs ⋕? x) :* mapEnvL cCxtTmDecL (delete x)
      _ → return $ None :* id
    e₁ᴱ :* τ₁ ← case τ'O of
      None → elabExpInfer e₁
      Some τ₁ → do
        e₁ᴱ ← elabExpCheck τ₁ e₁
        return $ e₁ᴱ :* τ₁
    e₂ᴱ ← f $ bindPat ψ τ₁ $ elabExpCheck τ e₂
    return $ LetE ψ e₁ᴱ e₂ᴱ
  _ → do
    eᴱ :* τ' ← elabExpInfer e
    when (τ' ≢ τ) $ \ _ →
      throwCErrorCxt TypeError "elabExpCheck: elabExpInfer: τ' ≢ τ" $ frhs
        [ ("τ'",pretty τ')
        , ("τ",pretty τ)
        ]
    return $ extract eᴱ

elabTL ∷ TL → CTLM ()
elabTL tl = case extract tl of
  PrinTL ρs → do
    let pρs = pow ρs
    ρs' ← getL ctlStatePrinsL
    when (pρs ∩ ρs' ≢ pø) $ \ _ → 
      throwCError (Some $ annotatedTag tl) TypeError "elabTL: PrinTL: pρs ∩ ρs' ≢ ∅" $ frhs
        [ ("pρs",pretty pρs)
        , ("ρs'",pretty ρs')
        ]
    putL ctlStatePrinsL $ pρs ∪ ρs'
  DeclTL x τ → do
    modifyL ctlStateTmDecL ((x ↦ τ) ⩌)
  DefnTL x ψs e → do
    let e' = buildLambda (annotatedTag tl) x ψs e
    xτs ← getL ctlStateTmDecL
    η :* e'τ' ← case xτs ⋕? x of
      Some τ → do
        modifyL ctlStateTmDecL (delete x)
        asCTLM $ do
          eᴱ' ← elabExpCheck τ e'
          return $ eᴱ' :* τ
      None → asCTLM $ elabExpInfer e'
    when (η ≢ null) $ \ _ → 
      throwCError (Some $ annotatedTag tl) TypeError "elabTL: DefnTL: η ≠ null" $ frhs
        [ ("η",pretty η)
        ]
    modifyL ctlStateTmEnvL ((x ↦ e'τ') ⩌)
  _ → throwCError (Some $ annotatedTag tl) NotImplementedError "elabTL" null

elabCTLs ∷ 𝐿 TL → CTLM ()
elabCTLs = eachWith elabTL

-------------
-- TESTING --
-------------

typecheckExample ∷ 𝕊 → IO (Exp ∧ Type)
typecheckExample fn = do
  let path = "examples/" ⧺ fn ⧺ ".psl"
  out path
  s ← read path
  let ts = tokens s
  ls ← tokenizeIO lexer ts
  tls ← parseIO cpTLs ls
  σtl ← evalCTLMIO σtl₀ $ retState $ elabCTLs tls
  return $ ctlStateTmEnv σtl ⋕! var "main"

testTypecheckerExample ∷ 𝕊 → IO ()
testTypecheckerExample fn = pprint *$ snd ^$ typecheckExample fn

testTypechecker ∷ IO ()
testTypechecker = do
  testTypecheckerExample "cmp"
  -- testTypecheckerExample "euclid2"

