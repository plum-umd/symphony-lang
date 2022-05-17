module Symphony.TypeChecker where

import Symphony.Prelude

import Symphony.Lang.Syntax

import Symphony.TypeChecker.Error
import Symphony.TypeChecker.TLM hiding (TLR)
import Symphony.TypeChecker.EM
import Symphony.TypeChecker.Operations

---------------------
-- Checking for TL --
---------------------

-- Gets the type of calling main  after doing binding
synProg ∷ STACK ⇒ 𝐿 TL → TLM Type
synProg prog = do
  eachOn prog bindTL
  asTLM $ synApp (nullExp (VarE (var "main"))) (nullExp (BulE))

bindTL ∷ STACK ⇒ TL → TLM ()
bindTL tl = localL ttlrSourceL (Some $ atag tl) $ bindTLR $ extract tl

-- Binds top level principals, declarations, and definitions
bindTLR ∷ STACK ⇒ TLR → TLM ()
bindTLR tlr = case tlr of
  PrinTL ρds          → bindPrins ρds
  DeclTL _brec x τ    → bindDecl x τ
  DefnTL _brec x ψs e → bindDefn x ψs e
  ImportTL _       → typeError "bindTLR: No imports should be allowed in top level tlr" $  frhs [ ("tlr", pretty tlr)]

bindDecl ∷ STACK ⇒ 𝕏 → Type → TLM ()
bindDecl = bindTypeTL

-- Binds definitions 
bindDefn ∷ STACK ⇒ 𝕏 → 𝐿 Pat → Exp → TLM ()
bindDefn x ψs e = asTLM $ do
  -- First it gets the type of the variable given it can be any mode
  τ ← localL terModeL Any $ synVar x
  case τ of
    -- If it is a function, it implicitly binds the variable as if there was a par block around the lambda
    -- Then it checks the function in that mode
    SecT _ (_ :→: (η :* _))   →
                  do
                    l₁ ← elabEMode $ effectMode η
                    localL terModeL l₁ $ (chkLam (Some x) ψs e τ)
    -- Otherwise it checks the function at top level
    _ →  (chkExp e τ)


-- Makes the principal a principal type located at type based on introduction typing rules
bindPrins ∷ STACK ⇒ STACK ⇒ 𝐿 PrinDecl → TLM ()
bindPrins ρds = eachOn ρds bindPrin
  where bindPrin ρd = case ρd of
          SinglePD ρ   →  do
            _ ← modifyL ttlsPrinsL ((single𝑃  (var ρ)) ∪)
            bindTypeTL (var ρ) $ (SecT Top (BaseT ℙT))
          ArrayPD _ _ → typeError "bindPrin: ρd is an array principal which is not allowed" $  frhs [ ("ρd", pretty ρd)]



------------------------------
-- Checking for Expressions --
------------------------------

-- ------ T-Var
-- Gets the well formed supertype of the type from x's context
synVar ∷ STACK ⇒ Var → EM Type
synVar x = do
  env ← askL terEnvL
  -- Uses the typing context
  case env ⋕? x of
    Some τ → do
      m ← askL terModeL
      bigM ← askL terModeScopeL
      -- gets the well formed supertype if there is one, if not error
      superty_wf τ m bigM
    None   → typeError "synVar: x ∉ Γ" $ frhs
             [ ("x", pretty x)
             , ("Γ", pretty $ keys env)
             ]


------------------
--- Primitives ---
------------------

-- All the literal rules are based in basic introduction rules
-- ------ T-Bt
-- gamma |- m bt : basetype@m

-- ------ T-Bul
-- gamma |- m () : bul@m
synBul ∷ STACK ⇒ EM Type
synBul =  do
  m ← askL terModeL
  em ← elabMode m
  return $ SecT em $ BaseT UnitT

-- ------ T-Bool
-- gamma |- m b : bool@m
synBool ∷ STACK ⇒  EM Type
synBool =  do
  m ← askL terModeL
  em ← elabMode m
  return $ SecT em $ BaseT 𝔹T

-- ------ T-Nat
-- gamma |- m n : nat@m
synNat ∷ STACK ⇒ IPrecision  → EM Type
synNat pr = do
  m ← askL terModeL
  em ← elabMode m
  return $ SecT em $ BaseT $ ℕT pr

-- ------ T-Int
-- gamma |- m i : int@m
synInt ∷ STACK ⇒ IPrecision → EM Type
synInt pr = do
  m ← askL terModeL
  em ← elabMode m
  return $ SecT em $ BaseT $ ℤT pr

-- ------ T-Float
-- gamma |- m d : float@m
synFlt ∷ STACK ⇒ FPrecision → EM Type
synFlt pr = do
  m ← askL terModeL
  em ← elabMode m
  return $ SecT em $ BaseT $ 𝔽T pr

-- ------ T-String
-- gamma |- m s : string@m
synStr ∷ STACK ⇒  EM Type
synStr = do
  m ← askL terModeL
  em ← elabMode m
  return $ SecT em $ BaseT 𝕊T

-- gamma(x) = t
-- ------ T-PrinExp
-- gamma |- m b : t

-- Basic introduction rule, but also checks and returns a type
synPrinExp ∷ STACK ⇒ PrinExp → EM Type
synPrinExp ρe = case ρe of
  VarPE x       → do
    ρτ ← (synVar x)
    m ← askL terModeL
    em ← elabMode m
    subcond ← (subtype ρτ (SecT em (BaseT ℙT)) pø )
    guardErr subcond $
      typeError "synPrinExp: ρe has type ρτ which is not a subtype of τ" $ frhs
        [ ("ρτ", pretty ρe)
        , ("ρτ'", pretty ρτ)
        , ("τ'", pretty (SecT em (BaseT ℙT)))
        ]
    return (SecT em (BaseT ℙT))
  AccessPE _ _ → typeError "synPrinExp: ρe is an access principal which is not allowed" $  frhs [ (" ρe", pretty ρe)]


-- forall A in M = {A ...} gamma |- m A t t : prin@m
-- ------T-PrinSetExp
-- gamma |- m A : ps@m
synPrinSet ∷ STACK ⇒ PrinSetExp → EM Type
synPrinSet ρse =
  case ρse of
    -- If it is a variable, checks it is a subtype of the basic introduction type
  VarPSE x → do
    ρsτ ← (synVar x)
    m ← askL terModeL
    em ← elabMode m
    subcond ← (subtype ρsτ (SecT em (BaseT ℙsT)) pø )
    guardErr subcond $
      typeError "synPrinSet: ρse has type ρsτ which is not a subtype of τ" $ frhs
        [ ("ρse", pretty ρse)
        , ("ρsτ'", pretty ρsτ)
        , ("τ'", pretty (SecT em (BaseT ℙT)))
        ]
    return ρsτ
  -- If it a powerset, check all the variables in the powerset of type principal set
  PowPSE ρes → do
    _ ←  mapM synPrinExp ρes
    m ← askL terModeL
    em ← elabMode m
    return $ SecT em $ BaseT ℙsT
  _    →  typeError "synPrinSet: ρse must be a variable or a powerset" $ frhs [("ρse", pretty ρse)]

-- T-Op
--m <= m_i since it could be a subtype which means
-- but it is guaranteed m_i >= m since it is well formed so m = m

-- If there is one but not all cleartext, all of them get converted to the same phi
-- gamma |- m e1 : sigma1^phi@m
-- gamma |- m e2 : sigma2^phi@m
-- ....
-- gamma |- m en : sigman^pih@mn
-- phi must be well formed
-- op [sigma1, sigma2 ... sigman] : sigma
-- --------
-- gamma|- m op [e1, e2, ..., en] : : sigma^phi@m

-- Based on T-Op
synPrim ∷ STACK ⇒ Op → 𝐿 Exp → EM Type
synPrim op es =
  -- If there are no arguments, get the type and return it with the introduction rule
  if (isEmpty es) then
     do
       m ← askL terModeL
       em ← elabMode m
       -- the return type
       bt ← primType op $ empty𝐿
       return $ SecT em $ BaseT bt
  else
    do
      m ← askL terModeL
      em ← elabMode m
      τs ← mapM synExp es
      -- Checks it ends with m (all types are well formed so no need to worry about)
      _ ← mapM (assertM m) τs
      -- Gets protocol options (Some p if encrypted, None if cleartext)
      pos ← mapM extractProt τs
      bs ← mapM extractBase τs
      -- The return type
      bt ← (primType op bs)
      let ps = list𝐼 (filterMap id pos) in
        case ps  of
          -- If all are cleartext, return the return type
          Nil → return $ SecT em $ BaseT bt
          -- Check that all protocols and encrpyted locations are the same and equal to m
          -- meaning the protoocl is well formed
          -- The encrypted location may not be necessary as wwe already asserted m
          -- But well formed don't disallow it so we'll keep it
          ((p, _) :& _) → do
            guardErr (and (map (\(p', l) -> (p ≡ p') ⩓  (eq_mode l m)) ps)) $
              typeError "synPrin: Not all protocols/encryptions are the same as p#loc" $ frhs
                [ ("ρ", pretty p)
                , ("loc'", pretty m)
                ]
            return $ SecT em $ ShareT p em $ BaseT bt


---------------------------------
--- Products, Sums, and Lists ---
---------------------------------

--Gets the type of the first, gets type of the second, returns the pair located value
-- T-Prod
-- gamma |- m e1 : t1
-- gamma |- m e2 : t2
-- --------
-- gamma |- m (e1, e2) : (t1 x t2) @m
synProd ∷ STACK ⇒  Exp → Exp → EM Type
synProd eₗ eᵣ =
  let cₗ = synExp eₗ
      cᵣ = synExp eᵣ
  in do
    τₗ ← cₗ
    τᵣ ← cᵣ
    m ← askL terModeL
    em ← elabMode m
    return $ SecT em $ (τₗ :×: τᵣ)

-- gamma |- m e : t |- m t' (already assumed since it is wellformed)
-- ------T-Inj
-- gamma |- m i1 e: (t + t')@m
chkL ∷ STACK ⇒ Exp → Type → EM ()
chkL eₗ τ  =
  case τ of
    (SecT _ (τₗ  :+: _)) → do
      -- Since the type is well formed, no subset check is needed
      _ ← chkExp eₗ τₗ
      return ()
    _ → typeError "chkL: τ is not annotated correctly as a located sumtype" $ frhs [ ("τ'", pretty τ)]

-- gamma |- m e : t |- m t' (already assumed since it is wellformed)
-- ------T-Inj
-- gamma |- m i2 e: (t' + t)@m
chkR ∷ STACK ⇒ Exp → Type → EM ()
chkR eᵣ τ  =
  case τ of
    -- Since the type is well formed, no subset check is needed
    (SecT _ (_  :+: τᵣ)) → do
      _ ← chkExp eᵣ τᵣ
      return ()
    _ → typeError "chkR: τ is not annotated correctly as a located sumtype" $ frhs [ ("τ'", pretty τ)]

-- gamma |- m : t
-- t = (list t') @m
-- t is well formed in m
-- --------
-- gamma |- m (nil) : t
chkNil ∷ STACK ⇒ Type → EM ()
chkNil τ =
  case τ of
     -- Since the type is well formed, no subset check is needed
    SecT _ (ListT _)  → return ()
    _  → typeError "chkNil: τ is not annotated correctly as a located list" $ frhs [ ("τ'", pretty τ)]

-- T-Cons (t is the join of t' and t'')
-- gamma |- m e1 : t where t' <: t
-- gamma |- m e2 : list t'' @m' where t'' <: t and m' >= m
--------
-- gamma |- m (e1, e2) : (list t) @m
synCons ∷ STACK ⇒ Exp → Exp → EM Type
synCons eₕ eₜ =
  let cₕ = synExp eₕ
      cₜ = synExp eₜ
  in do
    τ  ← cₕ
    τs ← cₜ
    case τs of
      SecT loc (ListT τₜ)  →  do
        join_t ← (ty_join τ τₜ)
        -- loc is a subset of em due to well formedness check, so we know to use loc
        return $ SecT loc $  ListT join_t
      _ → typeError "synCons: eₜ is not a located list. It is of type τs" $ frhs
            [ ("eₜ'", pretty eₜ)
              , ("τs'", pretty τs)
            ]

-- gamma |- m e1 : bool@m
-- gamma |- m e2 : t
-- gamma |- m e3 : t
-- ------T-PrinSetExp
-- gamma |- m if e1 then e2 else e3 : t
synIf :: STACK ⇒ Exp → Exp → Exp → EM Type
synIf e₁ e₂ e₃ =
  let c₁ = synExp e₁
      c₂ = synExp e₂
      c₃ = synExp e₃
  in do
    τ₁  ← c₁
    τ₂ ← c₂
    τ₃ ← c₃
    m ← askL terModeL
    em  ← elabMode m
    subcond ← subtype τ₁ (SecT em (BaseT 𝔹T)) pø
    guardErr subcond $
      typeError "synIf: e₁ is not a subtype of type bool @ m" $ frhs
          [ ("m", pretty m),
            ("e₁", pretty e₁)
          ]
    ty_join τ₂ τ₃

-- (x|-> t1) union context |-m e : t2
synBind ∷ STACK ⇒ Type → (Pat ∧ Exp) → EM Type
synBind τ₁ (ψ :* e₂) =
  let c₂ = synExp e₂
  in do
    f  ← bindType τ₁ ψ
    f c₂

-- T-Case (t is the join of t', t'', .... t'n)
-- gamma |- m e : t_e@m' where m' <= m
-- gamma updated_1 |- m e1 : t' where t'  <: t
-- gamma updated_2 |- m e2 : t'' where t'' <: t
-- ...
--gamma updated_n |- m en : t'n where t'n <: t
synCase ∷ STACK ⇒ Exp → 𝐿 (Pat ∧ Exp) → EM Type
synCase e ψes =
  let c = synExp e
  in do
    τ  ← c
    _  ← cleartext_type τ
    case τ of
      (SecT loc _) → do
        m ← askL terModeL
        l ← elabEMode loc
        -- Since τ is well formed, we just need to check l ≢  m
        guardErr (eq_mode m l) $
          typeError "synCase: ⊢ₘ e ˡ→ sigma@m ; m ≢ l" $ frhs
          [ ("e", pretty e)
          , ("m", pretty m)
          , ("l", pretty l)
          ]
        τs ← mapM (synBind τ) ψes
        (joinList τs)
      _ →  typeError "synCase: e is not a located type. It is of type τ" $ frhs
            [ ("e'", pretty e)
              , ("τ'", pretty τ)
            ]
-----------------
--- Functions ---
-----------------

--  |-m e1 t1
-- (x|-> t1) union context |-m e t2
-- ------T-Let
-- gamma |- m let x in e1 in e2 : t2
synLet ∷ STACK ⇒ Pat → Exp → Exp → EM Type
synLet ψ e₁ e₂ =
  let c₁ = synExp e₁
  in do
    τ₁ ← c₁
    synBind τ₁ (ψ :* e₂)


-- z|-> (t1 m -> t2)@m, x|-> t1) union context |-m e t2
-- ------T-Lam
-- gamma |- m lambda z x .e : (t1 m -> t2 )@m
chkLam ∷ STACK ⇒ 𝑂 Var → 𝐿 Pat → Exp →  Type → EM ()
chkLam self𝑂 ψs e τ =
  case τ of
    SecT loc (τ₁₁ :→: (η :* τ₁₂))   →
      case self𝑂 of
      None      →
                  do
                    m  ← askL terModeL
                    l₁ ← elabEMode $ effectMode η
                    l₂ ← elabEMode loc
                    -- Since τ is well formed, we just need to check the locations ≢  m
                    guardErr (eq_mode m l₁) $
                      typeError "chkLam: m ≢ l₁ in τ = (t₁ -> l₂ t₂)@l₁" $ frhs
                      [ ("m", pretty m)
                      , ("l₁", pretty l₁)
                      , ("τ", pretty τ)
                      ]
                    guardErr (eq_mode m l₂) $
                      typeError  "chkLam: m ≢ l₂ in τ = (t₁ -> l₂ t₂)@l₁" $ frhs
                      [ ("m", pretty m)
                      , ("l₂", pretty l₂)
                      , ("τ", pretty τ)
                      ]
                    -- Determines whether to check the lambda again with one less paramether
                    case ψs of
                      Nil → do
                        chkExp e τ₁₂
                      ψ :& Nil → do
                        bind ←  bindType τ₁₁ ψ
                        bind $ chkExp e τ₁₂

                      ψ :& ψs → do
                        bind ←  bindType τ₁₁ ψ
                        bind $ chkLam None ψs e τ₁₂
      -- Function with a recursive version is same as function with none and the recursive function name boudned
      Some self → (bindTo self τ) (chkLam None ψs e τ)
    _  → typeError "chkR: τ is not annotated correctly as a located function type" $ frhs [ ("τ'", pretty τ)]



--  |-m e1 ( t1 m -> t2)
--  |-m e2 t₂
-- ------T-App
-- gamma |- m e1 e2 : t2
synApp ∷ STACK ⇒ Exp → Exp → EM Type
synApp e₁ e₂ =
  let c₁ = synExp e₁
  in do
    τ₁ ← c₁
    case τ₁ of
      SecT loc (τ₁₁ :→: (η :* τ₁₂)) → do
        m  ← askL terModeL
        l₁ ← elabEMode $ effectMode η
        l₂ ← elabEMode loc
        -- Since τ₁ is well formed, we just need to check the locations ≢  m
        guardErr (eq_mode m l₁) $
          typeError "synApp: ⊢ₘ e₁ ˡ→ (t₁ -> l₂ t₂)@l₁ ; m ≢ l₁" $ frhs
            [  ("e₁", pretty e₁)
            ,  ("m", pretty m)
            , ("l", pretty l₁)
          ]
        guardErr (eq_mode l₁ l₂) $
          typeError "synApp: ⊢ₘ e₁ ˡ→ (t₁ -> l₂ t₂)@l₁ ; m ≢ l₂" $ frhs
            [  ("e₁", pretty e₁)
            ,  ("m", pretty m)
            , ("l", pretty l₁)
          ]
        _ ← chkExp e₂ τ₁₁

        return τ₁₂
      _ → typeError "synApp: ⊢ₘ e₁ ˡ→ τ₁ which is not a function"  $ frhs
          [ ("τ₁", pretty τ₁)
          ]

----------------------
--- Read and Write ---
----------------------

synRead ∷ STACK ⇒ Type → Exp → EM Type
synRead τ e =
  let c = synExp e
  in do
    m ← askL terModeL
    em ← elabMode m
    -- Takes a type with no locations
    τ' ← makeCleartextType em τ False
    τ'' ← c
    _ ← case m of
      Any → return ()
      AddAny m'  → do
                    guardErr ( (map psize m') ≡ (AddTop 1)) $
                      typeError "synRead: ⊢ₘ ; |m| ≢  1" $ frhs
                        [  ("m", pretty m)]
                    return ()

    case τ'' of
      (SecT loc (BaseT 𝕊T))  →
        do
          l ← elabEMode loc
          guardErr (eq_mode m l) $
            typeError "synRead: ⊢ₘ  e ˡ→ 𝕊@l ; m ≢ l" $ frhs
              [ ("e", pretty e)
              , ("m", pretty m)
              , ("l", pretty l)
              ]
          return τ'
      _ →  typeError "synRead: ⊢ₘ  e ˡ→ τ which is not a located string" (frhs 
            [ ("τ", pretty τ)  
            , ("e", pretty e)])



synWrite ∷ STACK ⇒  Exp → Exp → EM Type
synWrite e₁ e₂ =
  let c₁ = synExp e₁
      c₂ = synExp e₂
  in do
    m ← askL terModeL
    τ₁ ← c₁
    τ₂ ← c₂
    _ ← case m of
      Any → return ()
      AddAny m'  → do
                    guardErr ( (map psize m') ≡ (AddTop 1)) $
                      typeError "synWrite: ⊢ₘ ; |m| ≢  1" $ frhs
                        [ ("m", pretty m)]
                    return ()
    case τ₁ of
      (SecT loc₁ _)  → do
          l₁ ← elabEMode loc₁
          guardErr (eq_mode m l₁) $
            typeError "synWrite: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
                , ("l", pretty l₁)
              ]
          case τ₂ of
            (SecT loc₂ (BaseT 𝕊T))  → do
                                      l₂ ← elabEMode loc₂
                                      guardErr (eq_mode m l₂) $
                                        typeError "synWrite: ⊢ₘ  e₂ ˡ→ 𝕊@l₂ ; m ≢ l₂" $ frhs
                                          [ ("e₂", pretty e₂)
                                          , ("m", pretty m)
                                          , ("l₂", pretty l₂)
                                          ]
                                      return τ₁
            _ →   typeError "synWrite: ⊢ₘ  e₂ ˡ→ τ₂ which is not a located string" (frhs 
                  [ ("τ₂", pretty τ₂)  
                  , ("e₂", pretty e₂)])

      _ →   typeError "synWrite: ⊢ₘ  e₁ˡ→ τ₁ which is not a located type" (frhs 
              [ ("τ₁", pretty τ₁)  
              , ("e₁", pretty e₁)])



-------------------
--- Type Annotations ---
-------------------

-- Does a check and returns the type
synAscr :: STACK ⇒ Exp → Type →  EM Type
synAscr e τ = do
  _ ← (chkExp e τ)
  return τ

-------------------
--- References ---
-------------------

--  |-m e t
-- ------T-Ref
-- gamma |- m ref RW#m e : t
synRef ∷ STACK ⇒ Exp → EM Type
synRef e =
  let c = synExp e
  in do
  τ ← c
  m  ← askL terModeL
  em ← elabMode m
  return $ SecT em (RefT (Some em) τ)

--  |-m e : (ref RO t)@m
-- ------T-Deref
-- gamma |- m !e : t
synRefRead ∷ STACK ⇒ Exp → EM Type
synRefRead e =
  let c = synExp e
  in do
    τ ← c
    case τ of
      -- None is subtype
      -- Writes are also read only so we do not need to care about the reference mode
      (SecT loc (RefT _ τ'))  → do
        m  ← askL terModeL
        l ← elabEMode loc
        guardErr (eq_mode m l) $
          typeError "synRefRead:  ⊢ₘ  e ˡ→ ref@l ; m ≢ l" $ frhs
                                          [ ("e", pretty e)
                                          , ("m", pretty m)
                                          , ("l", pretty l)
                                          ]
        return τ'
      _  → typeError "synRefRead:  ⊢ₘ  e ˡ→ τ which is not a located reference type" $ frhs
                                          [ ("e", pretty e)
                                          , ("τ", pretty τ)
                                          ]


--  |-m e1 : (ref RW#m t)@m
--  |-m e2 : t
-- ------T-Assign
-- gamma |- m e1 :=e2 : t
synRefWrite ∷ STACK ⇒ Exp → Exp → EM Type
synRefWrite e₁ e₂ =
  let c₁ = synExp e₁
      c₂ = synExp e₂
  in do
    τ₁  ← c₁
    τ₂ ← c₂
    case τ₁ of
      (SecT loc₁₁ (RefT (Some loc₁₂) τ₁'))  → do
        m  ← askL terModeL
        l₁₁ ← elabEMode loc₁₁
        l₁₂ ← elabEMode loc₁₂
        -- Does this due to reflexivity of sub-refl
        guardErr (eq_mode m l₁₁) $
          typeError "synRefWrite:  ⊢ₘ  e₁ ˡ→ ref#l₁₂@l₁₁ ; m ≢ ll₁₁" $ frhs
                                          [ ("e₁", pretty e₁)
                                          , ("m", pretty m)
                                          , ("l₁₁", pretty l₁₁)
                                          ]
        guardErr (eq_mode m l₁₂) $
          typeError "synRefWrite:  ⊢ₘ  e₁ ˡ→ ref#l₁₂@l₁₁ ; m ≢ l₁₂" $ frhs
                                          [ ("e₁", pretty e₁)
                                          , ("m", pretty m)
                                          , ("l₁₂", pretty l₁₂)
                                          ]
        (ty_join  τ₁' τ₂)

      _ → typeError "synRefWrite:  ⊢ₘ  e₁ ˡ→ τ which is not a located writeable reference type" $ frhs
                                          [ ("e₁", pretty e₁)
                                          , ("τ₁", pretty τ₁)
                                          ]

--  |-m e1  nat@m
-- |- m e2 t
-- ------T-Arr
-- gamma |- m arr e1 e2: arr rw#m 0 t
synArray ∷ STACK ⇒ Exp → Exp → EM Type
synArray e₁ e₂ =
  let c₁ = synExp e₁
      c₂ = synExp e₂
  in do
    τ₁  ← c₁
    τ₂ ← c₂
    case τ₁ of
      (SecT loc₁ (BaseT (ℕT _)))  → do
        m  ← askL terModeL
        l₁ ← elabEMode loc₁
        em ← elabMode m
        guardErr (eq_mode m l₁) $
          typeError "syArray: ⊢ₘ  e₁ ˡ→ ℕ@l₁ ; m ≢ l₁" $ frhs
            [ ("e₁", pretty e₁)
            , ("m", pretty m)
            , ("l₁", pretty l₁)
            ]
        return $ SecT em (ArrT (Some em) τ₂)
      _  →    typeError "syArray: ⊢ₘ  e₁ ˡ→  τ₁ ; τ₁ is not a located natural number" $ frhs
            [ ("e₁", pretty e₁)
            , ("τ₁", pretty τ₁)
            ]


--  |-m e1 : (arr RO _ t)@m (every array is RO)
--  |-m e2 : nat@m
-- ------T-Deref
-- gamma |- m !e : t
synArrayRead ∷ STACK ⇒ Exp → Exp → EM Type
synArrayRead e₁ e₂ =
  let c₁ = synExp e₁
      c₂ = synExp e₂
  in do
    τ₁ ← c₁
    τ₂ ← c₂
    case τ₁ of
      (SecT loc₁ (ArrT _ τ₁'))  → do
        m  ← askL terModeL
        l₁ ← elabEMode loc₁
        --  dont need subcond  ←  (subtype τ (SecT m (RefT t')))
        guardErr (eq_mode m l₁) $
          typeError "synArrayRead:  ⊢ₘ  e₁ ˡ→ arr@l₁ ; m ≢ l₁" $ frhs
                                          [ ("e₁", pretty e₁)
                                          , ("m", pretty m)
                                          , ("l", pretty l₁)
                                          ]

        case τ₂ of
          (SecT loc₂ (BaseT (ℕT _)))  → do
            l₂ ← elabEMode loc₂
            guardErr (eq_mode m l₂) $
               typeError "synArrayRead:  ⊢ₘ  e₂ ˡ→ ℕ@l ; m ≢ l₂" $ frhs
                                          [ ("e₂", pretty e₂)
                                          , ("m", pretty m)
                                          , ("l₂", pretty l₂)
                                          ]
            return τ₁'
          _  →  typeError "synArrayRead:  ⊢ₘ  e₂ ˡ→ τ₂ which is not a located natural" $ frhs
                                          [ ("e₂", pretty e₂)
                                          , ("τ₂", pretty τ₂)
                                          ]
      _  →   typeError "synArrayRead:  ⊢ₘ  e₁ ˡ→ τ₁ which is not a located array" $ frhs
                                          [ ("e₁", pretty e₁)
                                          , ("τ₁", pretty τ₁)
                                          ]


--  |-m e1 : (arr RW#m t)@m
--  |-m e2 : nat@m
--  |-m e3 : t
-- ------T-Assign
-- gamma |- m e1[e2]:=e3 : t
synArrayWrite ∷ STACK ⇒ Exp → Exp → Exp → EM Type
synArrayWrite e₁ e₂ e₃ =
  let c₁ = synExp e₁
      c₂ = synExp e₂
      c₃ = synExp e₃
  in do
    τ₁ ← c₁
    τ₂ ← c₂
    τ₃ ← c₃
    case τ₁ of
      -- Does this due to reflexivity of sub-refl
      (SecT loc₁₁ (ArrT (Some loc₁₂) τ₁'))  → do
        m  ← askL terModeL
        l₁₁ ← elabEMode loc₁₁
        l₁₂ ← elabEMode loc₁₂
        --  dont need subcond  ←  (subtype τ (SecT m (ArrT _ t')))
        guardErr (eq_mode m l₁₁) $
          typeError "synArrayWrite:  ⊢ₘ  e₁ ˡ→ arr#l₁₂@l₁₁ ; m ≢ ll₁₁" $ frhs
                                          [ ("e₁", pretty e₁)
                                          , ("m", pretty m)
                                          , ("l₁₁", pretty l₁₁)
                                          ]
        guardErr (eq_mode m l₁₂) $
          typeError "synArrayWrite:  ⊢ₘ  e₁ ˡ→ arr#l₁₂@l₁₁ ; m ≢ l₁₂" $ frhs
                                          [ ("e₁", pretty e₁)
                                          , ("m", pretty m)
                                          , ("l₁₂", pretty l₁₂)
                                          ]
        case τ₂ of
          (SecT loc₂ (BaseT (ℕT _)))  → do
            l₂ ← elabEMode loc₂
            guardErr (eq_mode m l₂) $
              typeError "synArrayWrite: m /≡ l₂" $ frhs
                [ ("m", pretty m)
                  , ("l₂", pretty l₂)
                ]
            (ty_join  τ₁' τ₃)
          _  →  typeError "synArrayWrite:  ⊢ₘ  e₂ ˡ→ τ₂ which is not a located natural" $ frhs
                                          [ ("e₂", pretty e₂)
                                          , ("τ₂", pretty τ₂)
                                          ]
      _  →   typeError "synArrayWrite:  ⊢ₘ  e₁ ˡ→ τ₁ which is not a located array" $ frhs
                                          [ ("e₁", pretty e₁)
                                          , ("τ₁", pretty τ₁)
                                          ]

--  |-m e1 : (arr RO t)@m (Any array)
-- ------T-Size
-- gamma |- m size e1 : nat
synArraySize ∷ STACK ⇒ Exp → EM Type
synArraySize e =
  let c = synExp e
  in do
    τ ← c
    case τ of
      SecT loc (ArrT _ _)  → do
          m  ← askL terModeL
          em ← elabMode m
          l ← elabEMode loc
          --  dont need subcond  ←  (subtype τ (SecT m (RefT t')))
          guardErr (eq_mode m l) $
            typeError "synArraySize:  e ˡ→ arr@l; m /≡ l" $ frhs
            [  ("e", pretty e)
            ,  ("m", pretty m)
            , ("l", pretty l)
            ]
          return (SecT em (BaseT (ℕT iprDefault)))
                                              
      _  →   typeError "synArraySize:  ⊢ₘ  e ˡ→ τ which is not a located array" $ frhs
                                          [ ("e", pretty e)
                                          , ("τ", pretty τ)
                                          ]


-----------
--- Par ---
-----------

--  |-m union p e : t
--  m  union p != empty set
-- ------T-Par
-- gamma |- par [p] e : t
synPar ∷ STACK ⇒  PrinSetExp → Exp → EM Type
synPar ρse₁ e₂ =
  let c₁ = synPrinSet ρse₁
      c₂ = synExp e₂
  in do
    _ ← c₁
    m  ← askL terModeL
    l ← elabEMode (AddTop ρse₁)
    let m' = inter_m m l
    if m' ≢  (AddAny (AddTop bot)) then
      localL terModeL m' c₂
    else
      --  |-empty t
      --  m  union p == empty set
    -- ------T-Par
      -- gamma |- par [p] e : t
      -- Default value
      return $ SecT (AddTop (PowPSE empty𝐿))  (BaseT UnitT)

chkPar ∷ STACK ⇒  PrinSetExp → Exp → Type → EM ()
chkPar ρse₁ e₂ τ=
  let c₁ = synPrinSet ρse₁
      c₂ = synExp e₂
  in do
    _ ← c₁
    m  ← askL terModeL
    l ← elabEMode (AddTop ρse₁)
    let m' = inter_m m l
    if m' ≢  (AddAny (AddTop bot)) then do
      τ' ← localL terModeL m' c₂
      subcond  ← subtype τ' τ pø
      guardErr subcond $
        typeError "chkPar: τ' is not a subtype of τ" $ frhs
          [ ("τ'", pretty τ')
          , ("τ", pretty τ)
          ]
      return ()
    else do
      bigM ← askL terModeScopeL
      _ ← (wf_type τ  (AddAny (AddTop pø)) bigM)
      return ()

--  |-m e : cleartext type @p
--  q != empty set and p union q = m and p is a principal
-- ------T-Share
-- gamma |- m share[p -> q] e : cleartext type that gets encrypted by q @ q
synShare ∷ STACK ⇒  Prot → Type → PrinSetExp → PrinSetExp → Exp → EM Type
synShare φ τ ρse₁ ρse₂ e₃ =
  let c₁ = synPrinSet ρse₁
      c₂ = synPrinSet ρse₂
      in do
        _ ← c₁
        _ ← c₂
        m  ← askL terModeL
        p ←  elabEMode (AddTop (ρse₁))
        qs ← elabPrinSetExp ρse₂
        q ←  elabEMode (AddTop ρse₂)
        _ <-  case qs of
              (Inl inner_qs) → do
                          guardErr (not (isEmpty  inner_qs)) $
                            typeError "synShare: share[p -> q] e is not well typed: q is empty" $ frhs
                              [  ("q", pretty inner_qs)
                              ]
                          return ()
              _  → return ()

         -- Makes a cleartext version of the given type without locations
        cleartextτ ← (makeCleartextType (AddTop ρse₁) τ False)
        _ ←  localL terModeL m (chkExp e₃ cleartextτ)
        guardErr (eq_mode (union_m p q)  m ) $
          typeError "synShare: ⊢ₘ  share[p -> q] e is not well typed: p union q /= m" $ frhs
            [
              ("p", pretty p)
              , ("q", pretty q)
              , ("puq", pretty (union_m p q))
              , ("m", pretty m)
            ]
        -- Returns an encrypted version (with array mode changed) of the given type without locations
        (makeEncryptedType (AddTop ρse₂) φ τ True)

---  |-m e : encrypted by p type @p
--  q != empty set since it is a principal and p union q = m
-- ------T-Share
-- gamma |- m reveal[p -> q] e : cleartext type@ q
synReveal ∷ STACK ⇒ Prot → Type → PrinSetExp → PrinSetExp → Exp → EM Type
synReveal φ τ ρse₁ ρse₂ e₃ =
  let c₁ = synPrinSet ρse₁
      c₂ = synPrinSet ρse₂
      in do
        _ ← c₁
        _ ← c₂
        m  ← askL terModeL
        p ←  elabEMode (AddTop ρse₁)
        q ←  elabEMode (AddTop ρse₂)
         -- Makes an encrypted version of the given type without locations
        encryptedτ ← (makeEncryptedType (AddTop ρse₁) φ τ False)
        _  ←  localL terModeL m (chkExp e₃ encryptedτ)
        guardErr (eq_mode (union_m p q)  m ) $
          typeError "synReveal: ⊢ₘ  reveal[p -> q] e is not well typed: p union q /= m" $ frhs
            [
              ("p", pretty p)
              , ("q", pretty q)
              , ("puq", pretty (union_m p q))
              , ("m", pretty m)
            ]
         -- Returns a cleartext version (with array mode changed) of the given type without locations
        (makeCleartextType (AddTop ρse₂) τ True)


--  |-m e : cleartext type @p
--  q != empty set and p union q = m and p is a principal
-- ------T-Comm
-- gamma |- m comm[p -> q] e : cleartext type @ q
synComm∷ STACK ⇒  Type → PrinSetExp → PrinSetExp → Exp → EM Type
synComm τ ρse₁ ρse₂ e₃ =
  let c₁ = synPrinSet ρse₁
      c₂ = synPrinSet ρse₂
      in do
        _ ← c₁
        _ ← c₂
        m  ← askL terModeL
        p ←  elabEMode (AddTop ρse₁)
        qs ← elabPrinSetExp ρse₂
        q ←  elabEMode (AddTop ρse₂)
        _ <-  case qs of
                (Inl inner_qs) → do
                            guardErr (not (isEmpty  inner_qs)) $
                              typeError "syncComm: comm [p -> q] e is not well typed: q is empty" $ frhs
                              [ ("q", pretty qs)
                              ]
                            return ()
                _  → return ()

        cleartextτ ← (makeCleartextType (AddTop ρse₁) τ False)
        _  ←  localL terModeL m (chkExp e₃ cleartextτ)
        guardErr (eq_mode (union_m p q)  m ) $
          typeError "synComm: share[p -> q] e is not well typed: p union q /= m" $ frhs
            [
              ("p", pretty p)
              , ("q", pretty q)
              , ("puq", pretty (union_m p q))
              , ("m", pretty m)
            ]
        -- Returns a cleartext version (with array mode changed) of the given type without locations
        (makeCleartextType (AddTop ρse₂) τ True)

-- If there is one but not all cleartext, all of them get converted to the same phi
-- gamma |- m e1 : bool^phi@m
-- gamma |- m e2 : sigma^phi@m
-- gamma |- m e3 : sigma^pih@mn
-- phi must be well formed
-- --------
-- gamma|- m muxif e1 e2 e3 : : sigma^phi@m
synMuxIf ∷ STACK ⇒  Exp → Exp → Exp → EM Type
synMuxIf e₁ e₂ e₃ =do
      m ← askL terModeL
      em ← elabMode m
      τs ← (mapM synExp (frhs [e₁, e₂, e₃]) )
      _ ← (mapM assertShareable τs)
      _ ← (mapM (assertM m) τs)
      pos ← (mapM extractProt τs)
      let ps = list𝐼 (filterMap id pos) in
        if (isEmpty ps) then
          do
            case τs of
              (τ₁ :& (τ₂ :& (τ₃ :& Nil))) → do
                subcond  ← (subtype τ₁ (SecT em (BaseT 𝔹T)) pø  )
                guardErr subcond $
                  typeError "synMuxIf:  ⊢ₘ  e₁ ˡ→ τ₁ which is not a cleartext located boolean" $ frhs
                                          [ ("e₁", pretty e₁)
                                          , ("τ₁", pretty τ₁)
                                          ]
                (ty_join τ₂ τ₃)
              _  → undefined 
        else
          case ps  of
            ((p, _) :& _) → do
              guardErr (and (map (\(p', l) -> (p ≡ p') ⩓  (eq_mode l m)) ps)) $
                typeError "synMuxIf: Not all protocols/encryptions of  es' types  τs are the same as p#m" $ frhs
                  [ ("ρ", pretty p)
                  , ("m'", pretty m)
                  , ("τs", pretty τs)
                  , ("es", pretty [e₁, e₂, e₃])
                  ]
              eτs ← (mapM (embedShare p em) τs )
              case eτs of
                (τ₁ :& (τ₂ :& (τ₃ :& Nil))) → do
                  subcond  ← (subtype τ₁ (SecT em (ShareT p em (BaseT 𝔹T))) pø  )
                  guardErr subcond $
                    typeError "synMuxIf:  ⊢ₘ  e₁ ˡ→ τ₁ which is not a shared located boolean" $ frhs
                                  [ ("e₁", pretty e₁)
                                  , ("τ₁", pretty τ₁)
                                  ]
                  (ty_join τ₂ τ₃)
                _  → undefined 

-- If there is one but not all cleartext, all of them get converted to the same phi
-- Exceot us the furst
-- T-Case (t is the join of t', t'', .... t'n)
-- gamma |- m e : t_e@m' where m' <= m
-- gamma updated_1 |- m e1 : sigma^phi@ms
-- gamma updated_2 |- m e2 : sigma^pih@mn
-- ...
--gamma updated_n |- m en : sigma^pih@mn
-- phi must be well formed
-- --------
-- gamma|- m muxcase p1 e1 p2 e2 ... pn en : : sigma^phi@m
synMuxCase ∷ STACK ⇒  Exp → 𝐿 (Pat ∧ Exp) → EM Type
synMuxCase e ψes =do
  let c = synExp e in do
    τ  ← c
    m ← askL terModeL
    τs' ← mapM (synBind τ) ψes
    let τs = (τ :& τs') in do
      _ ← (mapM assertShareable τs)
      _ ← (mapM (assertM m) τs)
      pos ← (mapM extractProt τs)
      let ps = list𝐼 (filterMap id pos) in
        if (isEmpty ps) then
          (joinList τs')
        else
          case τ of
            (SecT em (ShareT _ _ _ )) →
              case ps  of
                ((p, _) :& _) → do
                  guardErr (and (map (\(p', l) -> (p ≡ p') ⩓  (eq_mode l m)) ps)) $
                    typeError "synMuxCase: Not all protocols/encryptions of es' types  τs are the same as p#m" $ frhs
                      [ ("ρ", pretty p)
                      , ("m'", pretty m)
                      , ("τs", pretty τs)
                      , ("es", pretty ψes)
                      ]
                  eτs' ← (mapM (embedShare p em) τs' )
                  (joinList eτs')
                _  → undefined
            _ → typeError "synMuxCase: The case expression's guard expression e of type τ is cleartext while the some of all of the bodies is not" $ frhs
                  [ ("e", pretty e)
                  , ("τ", pretty τ)
                  ]


-- Bundles
synBundleIntro :: STACK ⇒ (PrinExp ∧ Exp) → EM Type
synBundleIntro (pe :* e) =
  let c = synExp e
  in do
    τ ← c
    m  ← askL terModeL
    em ← elabMode m
    case τ of
      (SecT loc τ' ) → do
          p ←  elabEMode (AddTop (PowPSE (frhs [pe])))
          p' ← elabEMode loc
          guardErr (p ≡ p') $
            typeError "synBundleIntro: ⊢ₘ e → _@p'; <e, p> is not well typed: p /≡ p'" $ frhs
              [ ("p", pretty p)
              , ("p'", pretty p')
              ]
          return (SecT em (ISecT loc τ'))


synBundle ∷ STACK ⇒ 𝐿 (PrinExp ∧ Exp) → EM Type
synBundle ρee𝐿 =
  do
    τs ← (mapM synBundleIntro ρee𝐿)
    case τs of
      (τ :& τs') → (mfold τ synBundleUnionHelper τs')
      _ →   typeError "synBundle: An bundle with the empty list ρee𝐿 was given which is not implemented" $ frhs
              [ ("ρee𝐿", pretty ρee𝐿)
              ]

synBundleAccess ∷ STACK ⇒ Exp → PrinExp → EM Type
synBundleAccess e₁ ρe₂ =
  let c₁ = synExp e₁
      c₂ = synPrinExp ρe₂
  in do
    τ₁ ← c₁
    _ ← c₂
    guardErr (isEmbedable τ₁) $
      typeError "synBundleAccess: ⊢ₘ e₁ ˡ→ τ₁ which is not a embedable cleartext type'" $ frhs
      [ ("e₁", pretty τ₁)
      , ("τ₁", pretty τ₁)
      ]
    case τ₁ of
      (SecT loc₁ (ISecT loc₁' τ₁'))  → do
        m  ← askL terModeL
        l₁ ← elabEMode loc₁
        guardErr (eq_mode m l₁) $
          typeError "synBundleAccess: e₁ ˡ→ bundle#τ@q@l, m /≡ l" $ frhs
          [ ("m", pretty m)
          , ("l", pretty l₁)
          ]
        do
          q ← elabEMode loc₁'
          p ←  elabEMode (AddTop (PowPSE (frhs [ρe₂])))
          guardErr (supermode q p)  $
            typeError "synBundleAccess: BundleAcces e₁ p; e₁ ˡ→ bundle#τ@q@l: not p is not a subset of q" $ frhs
            [ ("p", pretty p)
              , ("q", pretty q)
            ]
          return (SecT (AddTop (PowPSE (frhs [ρe₂]))) τ₁')

synBundleUnion ∷ STACK ⇒ Exp → Exp → EM Type
synBundleUnion e₁ e₂ =
  let c₁ = synExp e₁
      c₂ = synExp e₂
  in do
    τ₁ ← c₁
    τ₂ ← c₂
    synBundleUnionHelper τ₁ τ₂


synBundleUnionHelper ∷ STACK ⇒ Type → Type → EM Type
synBundleUnionHelper τ₁ τ₂ =

    case τ₁ of
      (SecT loc₁ (ISecT loc₁' τ₁'))  → do
        guardErr (isEmbedable τ₁') $
          typeError "synBundleUnionHelper: ⊢ₘ τ₁ = bundle#τ₁'@p@l, where τ₁' is not a embedable cleartext type'" $ frhs
            [ ("τ₁'", pretty τ₁')
            ]
        m  ← askL terModeL
        l₁ ← elabEMode loc₁
        guardErr (m ≡ l₁) $
          typeError "synBundleUnionHelper: τ₁ = bundle#τ₁'@p@l,m /≡ l" $ frhs
          [ ("τ₁", pretty τ₁)
          , ("m", pretty m)
          , ("l", pretty l₁)
          ]
        case τ₂ of
          (SecT loc₂ (ISecT loc₂' τ₂'))  → do
            guardErr (isEmbedable τ₂') $
              typeError "synBundleUnionHelper: ⊢ₘ τ₂ = bundle#τ₁'@p@l, where τ₁' is not a embedable cleartext type'" $ frhs
              [ ("τ₂'", pretty τ₂')
              ]
            l₂ ← elabEMode loc₂
            guardErr (m ≡ l₂) $
              typeError "synBundleUnionHelper: τ₂ = bundle#τ₁'@p@l,m /≡ l" $ frhs
              [ ("τ₂", pretty τ₂')
                , ("m", pretty m)
                , ("l", pretty l₂)
              ]
            p₁ ← elabEMode loc₁'
            p₂ ← elabEMode loc₂'
            guardErr (inter_m p₁ p₂ ≡ (AddAny (AddTop bot))) $
              typeError "synBundleUnionHelper:  τ₁ = bundle#τ₁'@p₁@l,; τ₂ = bundle#τ₁'@p₂@l; p₁ ⊓ p₂ ≢  bot" $ frhs
              [ ("p₁", pretty p₁)
                , ("p₂", pretty p₂)
                ,  ("τ₁'", pretty τ₁')
                , ("τ₂", pretty τ₂)
              ]
            q ← elabMode (union_m p₁ p₂)
            τ ←  (locty_join τ₁' τ₂')
            return  (SecT loc₂ (ISecT q τ))
          _ →           typeError "synBundleUnionHelper: τ₂ is not a located bundle type'" $ frhs
              [ ("τ₂", pretty τ₁)
              ]
      _ →           typeError "synBundleUnionHelper: τ₁ is not a located bundle type'" $ frhs
              [ ("τ₁", pretty τ₁)
              ]

-------------------
--- Recursive Types ---
-------------------

-- u = (mu alpha. t)
-- gamma |- m e : [(mu alpha. t)/ alpha] t
-- ------T-Fold
-- gamma |- fold [u] x : u
chkFold ∷ STACK ⇒ Exp → Type → EM ()
chkFold e τ=
 case τ of
    (RecT a τ')   →  do
      substtype ←  type_subst a τ' τ
      _  ← chkExp e substtype
      return ()
    _  → typeError "chkFold: Type given τ is given is not a located recursive type" $ frhs [ ("τ'", pretty τ)]


-- u = (mu alpha. t)
-- gamma |- m e : [(mu alpha. t)/ alpha] t
-- ------T-Fold
-- gamma |- fold [u] x : u

synUnfold ∷ STACK ⇒  Exp →  EM Type
synUnfold e =
  let c = synExp e in do
    τ ← c
    case τ of
      (RecT a τ')   →  (type_subst a τ' τ)
      _  → typeError "synUnfold: ⊢ₘ e ˡ→ τ which is not a recursive type" $ frhs 
        [ ("e", pretty e)
        , ("τ'", pretty τ)]

-------------------
--- Universal Types ---
-------------------


-- gamma, X |- m e : T
-- ------T-TLam
-- gamma |- m lam X.e : forall X. e
synTLam ∷ STACK ⇒ TVar→ Exp → EM Type
synTLam x e  =
  let c = synExp e
      m' = AddAny (AddTop pø)
  in do

    τ ← (mapEnvL terModeScopeL ((x ↦ m') ⩌) c)
    m ← askL terModeL
    bigM ← askL terModeScopeL
    _ ← wf_type (ForallT x τ) m bigM
    return $ ForallT x τ

-- gamma, X |- m e : forall X.T1
-- ------T-TLam
-- gamma |- e [T] : [X |-> T] T1
synTApp ∷ STACK ⇒ Exp → Type →  EM Type
synTApp e τ =
  let c = synExp e
  in do
    m ← askL terModeL
    bigM ← askL terModeScopeL
    _ ← wf_type τ m bigM
    τ' ← c
    case τ' of
      (ForallT x τ₁') →  (type_subst x τ₁' τ)
      _ → typeError "synTApp: ⊢ₘ e ˡ→ τ which is not a forall type " $ frhs
            [ ("e", pretty e)
            , ("τ'", pretty τ')]

-------------------
--- Expressions ---
-------------------

chkExp :: STACK ⇒ Exp → Type → EM ()
chkExp e τ = 
  localL terSourceL (Some $ atag e) (chkExpR (extract e) τ)
  -- chkExpR (extract e) τ

chkExpR :: STACK ⇒ ExpR → Type → EM ()
chkExpR e τ =
  do
    m  ← askL terModeL
    bigM ← askL terModeScopeL
    -- Check it is well formed
    wfcond ← (wf_type τ m bigM)
    case e of
      LE eₗ        → chkL eₗ τ
      RE eᵣ        → chkR eᵣ τ
      NilE        → chkNil τ
      LamE self𝑂 ψs e → chkLam self𝑂 ψs e τ
      ParE ρse₁ e₂ → chkPar ρse₁ e₂ τ
      FoldE e → chkFold e τ
      _ →
          do
            τ' ← synExpR e
            subcond  ← (subtype τ' τ pø)
            guardErr subcond $
              typeError "chkExpR: synUnfold: ⊢ₘ e ˡ→ τ which is not a subtype of τ" $ frhs
              [ ("e", pretty e)
              , ("τ", pretty τ)
              , ("τ'", pretty τ')
              ]


synExp :: STACK ⇒ Exp → EM Type
synExp e = localL terSourceL (Some $ atag e) (synExpR (extract e))


synExpR ∷ STACK ⇒ ExpR → EM Type
synExpR e = case e of
   -- Variables
  VarE x → synVar x

  -- Literals--
  BulE        → synBul
  BoolE _     → synBool
  NatE pr _   → synNat pr
  IntE pr _   → synInt pr
  FltE pr _   → synFlt pr
  StrE _      → synStr
  PrinSetE es → synPrinSet es
  PrimE op es → synPrim op es

  ProdE eₗ eᵣ  → synProd eₗ eᵣ
  ConsE eₕ eₜ  → synCons eₕ eₜ
  IfE e₁ e₂ e₃ → synIf e₁ e₂ e₃
  CaseE e ψes  → synCase e ψes

  LetE ψ e₁ e₂    → synLet ψ e₁ e₂
  AppE e₁ e₂      → synApp e₁ e₂

  -- Read and Write
  ReadE τ e    → synRead τ e
  WriteE e₁ e₂ → synWrite e₁ e₂


  -- References
  RefE e          → synRef e
  RefReadE e      → synRefRead e
  RefWriteE e₁ e₂ → synRefWrite e₁ e₂

  -- Arrays
  ArrayE e₁ e₂                                → synArray e₁ e₂
  ArrayReadE e₁ e₂                            → synArrayRead e₁ e₂
  ArrayWriteE (extract → ArrayReadE e₁ e₂) e₃ → synArrayWrite e₁ e₂ e₃
  ArraySizeE e                                → synArraySize e

  -- Par
  ParE ρse₁ e₂ → synPar ρse₁ e₂

  AscrE e τ → synAscr e τ

    -- Share, Reveal, and Send
  ShareE φ τ ρse₁ ρse₂ e₃  → synShare φ τ ρse₁ ρse₂ e₃
  RevealE φ τ ρse₁ ρse₂ e₃ → synReveal φ τ ρse₁ ρse₂ e₃
  SendE τ ρse₁ ρse₂ e₃     → synComm τ ρse₁ ρse₂ e₃

  -- MPC Operations
  MuxIfE e₁ e₂ e₃ → synMuxIf e₁ e₂ e₃
  MuxCaseE e ψes  → synMuxCase e ψes

  -- Bundles
  BundleE ρees         → synBundle ρees
  BundleAccessE e₁ ρe₂ → synBundleAccess e₁ ρe₂
  BundleUnionE e₁ e₂   → synBundleUnion e₁ e₂

  UnfoldE  e → synUnfold e

  TLamE x e → synTLam x e
  TAppE e τ → synTApp e τ
  _      → undefined


---------------
-- Utilities --
---------------

-- By default, expression monads have top level checked at the top mode and no mode scope givin the environment and principals
asTLM ∷ STACK ⇒ EM a → TLM a
asTLM eM = do
  γ ← getL ttlsEnvL
  ps ← getL ttlsPrinsL
  let r = ER { terSource = None, terMode = (AddAny Top), terEnv = γ, terModeScope = dø, terPrins = ps }
  evalEMErr r () eM

-- Checks the type is well formed at top level and binds it
bindTypeTL ∷ STACK ⇒ 𝕏 → Type → TLM ()
bindTypeTL x τ = do
  _ ← (wf_typeTL τ)
  modifyL ttlsEnvL ((x ↦ τ) ⩌)

wf_typeTL ∷ STACK ⇒ Type → TLM ()
wf_typeTL τ = asTLM $
  case τ of
    -- A function at top level can be checked as well formed at any mode
    -- This assumes that a par block of that mode is implicitly put around 
    -- the function that is bounded to the variable
    -- Based on WF-Loc and WF-Fun given m == m' based on the fact we want to type check
    -- this function later
    SecT loc (τ₁₁ :→: (η :* τ₁₂))   →
                  do
                    l₁ ← elabEMode $ effectMode η
                    l₂ ← elabEMode loc
                    guardErr (eq_mode l₁ l₂) $
                      typeError " WFCheckTL: For τ = (τ₁₁ :→: (l₁ :* τ₁₂))@l₂, l₁ ≢ l₂ in τ" $ frhs
                      [ ("l₁", pretty l₂)
                      , ("l₂", pretty l₂)
                      , ("τ", pretty τ)
                      ]
                    (wf_type τ l₁ dø)
    -- Otherwise, a well formedness check will be done at the top mode always
    _ →  (wf_type τ (AddAny Top) dø)
