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

synProg ∷ STACK ⇒ 𝐿 TL → TLM Type
synProg prog = do
  eachOn prog bindTL
  asTLM $ do
    τMain ← synVar $ var "main"
    synApp (nullExp (VarE (var "main"))) (nullExp (BulE))

bindTL ∷ STACK ⇒ TL → TLM ()
bindTL tl = localL ttlrSourceL (Some $ atag tl) $ bindTLR $ extract tl

bindTLR ∷ STACK ⇒ TLR → TLM ()
bindTLR tlr = case tlr of
  PrinTL ρds          → bindPrins ρds
  DeclTL _brec x τ    → bindDecl x τ
  DefnTL _brec x ψs e → bindDefn x ψs e
  ImportTL path       → todoError

bindDecl ∷ STACK ⇒ 𝕏 → Type → TLM ()
bindDecl = bindTypeTL

bindDefn ∷ STACK ⇒ 𝕏 → 𝐿 Pat → Exp → TLM ()
bindDefn x ψs e = asTLM $ do
  τ ← synVar x
  case τ of
    SecT loc (τ₁₁ :→: (η :* τ₁₂))   →
                  do
                    l₁ ← elabEMode $ effectMode η
                    localL terModeL l₁ $ (checkLam (Some x) ψs e τ)
    _ →  (chkExp e τ)


bindPrins ∷ STACK ⇒ STACK ⇒ 𝐿 PrinDecl → TLM ()
bindPrins ρds = eachOn ρds bindPrin
  where bindPrin ρd = case ρd of
          SinglePD ρ   →  do
            _ ← modifyL ttlsPrinsL ((single𝑃  (var ρ)) ∪)
            bindTypeTL (var ρ) $ (SecT Top (BaseT ℙT))
     --     ArrayPD ρ _n → bindTypeTL (var ρ) $ (SecT Top (BaseT ℙsT))
{-
synAppTL ∷ STACK ⇒ Type → Type → EM Type
synAppTL τ₁ τ₂ = case τ₁ of
  SecT loc (τ₁₁ :→: (η :* τ₁₂)) → do
    m  ← askL terModeL
    l₁ ← elabEMode $ effectMode η
    l₂ ← elabEMode loc
    guardErr (eq_mode m l₁) $
      typeError "synApp: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
      [ ("m", pretty m)
      , ("l", pretty l₁)
      ]
    return τ₂
  _ → typeError "synApp: τ₁ ≢ (_ → _)@_" $ frhs
      [ ("τ₁", pretty τ₁)
      ]

synAppTL2 ∷ STACK ⇒ Type → Type → EM Type
synAppTL2 τ₁ τ₂ =
    case τ₁ of
      SecT loc (τ₁₁ :→: (η :* τ₁₂)) → do
        m  ← askL terModeL
        l₁ ← elabEMode $ effectMode η
        l₂ ← elabEMode loc
        subcond  ←  (subtype_embed τ₂ τ₁₂ pø )
        guardErr (eq_mode m l₁) $
          typeError "synApp: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
          [ ("m", pretty m)
          , ("l", pretty l₁)
          ]
        guardErr (eq_mode m l₂) $
          typeError "synApp: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
          [ ("m", pretty m)
          , ("l", pretty l₁)
          ]
        return τ₂
      _ → typeError "synApp: τ₁ ≢ (_ → _)@_" $ frhs
          [ ("τ₁", pretty τ₁)
          ]
-}


------------------------------
-- Checking for Expressions --
------------------------------

-- ------ T-Var
synVar ∷ STACK ⇒ Var → EM Type
synVar x = do
  env ← askL terEnvL
  case env ⋕? x of
    Some τ → do
      m ← askL terModeL
      bigM ← askL terModeScopeL
      -- T-Var: gets the well formed supertype if there is one, if not error
      superty_wf τ m bigM
    None   → typeError "synVar: x ∉ Γ" $ frhs
             [ ("x", pretty x)
             , ("Γ", pretty $ keys env)
             ]


------------------
--- Primitives ---
------------------

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
synBool ∷ STACK ⇒ 𝔹 → EM Type
synBool b =  do
  m ← askL terModeL
  em ← elabMode m
  return $ SecT em $ BaseT 𝔹T

-- ------ T-Nat
-- gamma |- m n : nat@m
synNat ∷ STACK ⇒ IPrecision → ℕ → EM Type
synNat pr n = do
  m ← askL terModeL
  em ← elabMode m
  return $ SecT em $ BaseT $ℕT pr

-- ------ T-Int
-- gamma |- m i : int@m
synInt ∷ STACK ⇒ IPrecision → ℤ → EM Type
synInt pr z = do
  m ← askL terModeL
  em ← elabMode m
  return $ SecT em $ BaseT $ ℤT pr

-- ------ T-Float
-- gamma |- m d : float@m
synFlt ∷ STACK ⇒ FPrecision → 𝔻 → EM Type
synFlt pr d = do
  m ← askL terModeL
  em ← elabMode m
  return $ SecT em $ BaseT $ 𝔽T pr

-- ------ T-String
-- gamma |- m s : string@m
synStr ∷ STACK ⇒  𝕊 → EM Type
synStr s = do
  m ← askL terModeL
  em ← elabMode m
  return $ SecT em $ BaseT 𝕊T

-- gamma(x) = t
-- ------ T-PrinExp
-- gamma |- m b : t
synPrinExp ∷ STACK ⇒ PrinExp → EM Type
synPrinExp ρe = case ρe of
  VarPE x       → do
    ρτ ← (synVar x)
    m ← askL terModeL
    em ← elabMode m
    subcond ← (subtype_embed ρτ (SecT em (BaseT ℙT)) pø )
    guardErr subcond $
      typeError "checkPrin: ρe has type ρτ which is not a subtype of τ" $ frhs
        [ ("ρτ", pretty ρe)
        , ("ρτ'", pretty ρτ)
        , ("τ'", pretty (SecT em (BaseT ℙT)))
        ]
    return ρτ
  AccessPE x n₁ → todoError

{-
-- forall A in M = {A ...} gamma |- m A t t <: prin@all
checkPrin ∷ STACK ⇒ PrinExp → EM ()
checkPrin ρe =
   do
    ρτ ← (synVar ρe)
    m ← askL terModeL
    em ← elabMode m
    subcond ← (subtype_embed ρτ (SecT em (BaseT ℙT)) pø )
    guardErr subcond $
      typeError "checkPrin: ρe has type ρτ which is not a subtype of τ" $ frhs
        [ ("ρτ", pretty ρe)
        , ("ρτ'", pretty ρτ)
        , ("τ'", pretty (SecT em (BaseT ℙT)))
        ]
    return ()
-}

-- forall A in M = {A ...} gamma |- m A t t : prin@m
-- ------T-PrinSetExp
-- gamma |- m A : ps@m
synPrinSet ∷ STACK ⇒ PrinSetExp → EM Type
synPrinSet ρse =
  case ρse of
  VarPSE x → do
    ρsτ ← (synVar x)
    m ← askL terModeL
    em ← elabMode m
    subcond ← (subtype_embed ρsτ (SecT em (BaseT ℙsT)) pø )
    guardErr subcond $
      typeError "synPrinSet: ρse has type ρsτ which is not a subtype of τ" $ frhs
        [ ("ρse", pretty ρse)
        , ("ρsτ'", pretty ρsτ)
        , ("τ'", pretty (SecT em (BaseT ℙT)))
        ]
    return ρsτ
  PowPSE ρes → do
    _ ←  mapM synPrinExp ρes
    m ← askL terModeL
    em ← elabMode m
    return $ SecT em $ BaseT ℙsT
  _    →  typeError "Must be a set of literals" $ frhs [("ρse", pretty ρse)]

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

synPrim ∷ STACK ⇒ Op → 𝐿 Exp → EM Type
synPrim op es =
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
        -- If all are cleartext, return the return type
        if (isEmpty ps) then
          return $ SecT em $ BaseT bt
        else
          case ps  of
            -- Check that all protocols and encrpyted locations are the same and equal to m
            -- meaning the protoocl is well formed
            -- The encrypted location may not be necessary as wwe already asserted m
            -- But well formed don't disallow it so we'll keep it
            ((p, loc) :& _) → do
              guardErr (and (map (\(p', l) -> (p ≡ p') ⩓  (eq_mode l m)) ps)) $
                typeError "Not all protocols/encryptions are the same as p#loc" $ frhs
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
checkL ∷ STACK ⇒ Exp → Type → EM ()
checkL eₗ τ  =
  case τ of
    (SecT em (τₗ  :+: _)) →do
      _ ← chkExp eₗ τₗ
      return ()
    _ → typeError "checkL: τ is not annotated correctly as a sumtype" $ frhs [ ("τ'", pretty τ)]

-- gamma |- m e : t |- m t' (already assumed since it is wellformed)
-- ------T-Inj
-- gamma |- m i2 e: (t' + t)@m
checkR ∷ STACK ⇒ Exp → Type → EM ()
checkR eᵣ τ  =
  case τ of
    (SecT em (_  :+: τᵣ)) → do
      _ ← chkExp eᵣ τᵣ
      return ()
    _ → typeError "checkR: τ is not annotated correctly as a sumtype" $ frhs [ ("τ'", pretty τ)]

-- gamma |- m : t
-- t = (list t') @m
-- t is well formed in m
-- --------
-- gamma |- m (nil) : t
checkNil ∷ STACK ⇒ Type → EM ()
checkNil τ =
  case τ of
    SecT em (ListT τₜ)  → return ()
    x  → todoError

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
      SecT em' (ListT τₜ)  →  do
        m ← askL terModeL
        em ← elabMode m
        join_t ← (ty_join τ  τₜ)
        em'' ← (inter_em em' em)
        return $ SecT em'' $  ListT join_t
      _ → typeError "synCons: eₜ is not a located list. It is of type " $ frhs
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
    subcond ← subtype_embed τ₁ (SecT em (BaseT 𝔹T)) pø
    guardErr subcond $
      typeError "synIf: e₁ is not of type bool @ m" $ frhs
          [ ("m", pretty m),
            ("e₁", pretty e₁)
          ]
    ty_join τ₂ τ₃


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
    case τ of
      (SecT loc (ShareT _ _ _)) → todoError
      (SecT loc _) → do
        m ← askL terModeL
        l ← elabEMode loc
        guardErr (eq_mode m l) $
          typeError "synCase: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
          [ ("m", pretty m)
          , ("l", pretty l)
          ]
        τs ← mapM (synBind τ) ψes
        (joinList τs)
-- (x|-> t1) union context |-m e : t2
synBind ∷ STACK ⇒ Type → (Pat ∧ Exp) → EM Type
synBind τ₁ (ψ :* e₂) =
  let c₂ = synExp e₂
  in do
    f  ← bindType τ₁ ψ
    f c₂
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
checkLam ∷ STACK ⇒ 𝑂 Var → 𝐿 Pat → Exp →  Type → EM ()
checkLam self𝑂 ψs e τ =
  case τ of
    SecT loc (τ₁₁ :→: (η :* τ₁₂))   →
      case self𝑂 of
      None      →
                  do
                    m  ← askL terModeL
                    l₁ ← elabEMode $ effectMode η
                    l₂ ← elabEMode loc
                    guardErr (eq_mode m l₁) $
                      typeError "checkLam: ⊢ₘ _ ˡ→ _ ; m ≢ l₁ in τ" $ frhs
                      [ ("m", pretty m)
                      , ("l₁", pretty l₁)
                      , ("τ", pretty τ)
                      ]
                    guardErr (eq_mode m l₂) $
                      typeError "checkLam: ⊢ₘ _ ˡ→ _ ; m ≢ l₂ in τ" $ frhs
                      [ ("m", pretty m)
                      , ("l₂", pretty l₂)
                      , ("τ", pretty τ)
                      ]
                    case ψs of
                      Nil → do
                        chkExp e τ₁₂
                      ψ :& Nil → do
                        bind ←  bindType τ₁₁ ψ
                        bind $ chkExp e τ₁₂

                      ψ :& ψs → do
                        bind ←  bindType τ₁₁ ψ
                        bind $ checkLam None ψs e τ₁₂


      Some self → (bindTo self τ) (checkLam None ψs e τ)
    _  → typeError "checkLam: Not annotated correctly" $ frhs [ ("τ'", pretty τ)]



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
        guardErr (eq_mode m l₁) $
          typeError "synApp: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
            [ ("m", pretty m)
            , ("l", pretty l₁)
          ]
        guardErr (eq_mode l₁ l₂) $
          typeError "synApp: ⊢ₘ _ ˡ→ _ ; m ≢ l₂" $ frhs
          [ ("m", pretty m)
          , ("l", pretty l₂)
          ]
        _ ← chkExp e₂ τ₁₁

        return τ₁₂
      _ → typeError "synApp: τ₁ ≢ (_ → _)@_" $ frhs
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
    τ' ← makeCleartextType em τ False
    τ'' ← c
    _ ← case m of
      Any → return ()
      AddAny m'  → do
                    guardErr ( (map psize m') ≡ (AddTop 1)) $
                      typeError "synRead: ⊢ₘ ; |m| ≢  1" $ frhs
                        [ ("m", pretty m)
                        ]
                    return ()

    case τ'' of
      (SecT loc (BaseT 𝕊T))  →
        do
          l ← elabEMode loc
          guardErr (eq_mode m l) $
            typeError "synRead: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
                , ("l", pretty l)
              ]
          return τ'
      _ →  typeError "synRead: ; e not a string" (frhs [("e", pretty e)])



synWrite ∷ STACK ⇒  Exp → Exp → EM Type
synWrite e₁ e₂ =
  let c₁ = synExp e₁
      c₂ = synExp e₂
  in do
    m ← askL terModeL
    τ ← c₁
    τ' ← c₂
    _ ← case m of
      Any → return ()
      AddAny m'  → do
                    guardErr ( (map psize m') ≡ (AddTop 1)) $
                      typeError "synWrite: ⊢ₘ ; |m| ≢  1" $ frhs
                        [ ("m", pretty m)
                        ]
                    return ()
    case τ of
      (SecT loc bτ)  → do
          l₁ ← elabEMode loc
          guardErr (eq_mode m l₁) $
            typeError "synWRite: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
                , ("l", pretty l₁)
              ]
          case τ' of
            (SecT loc' (BaseT 𝕊T))  → do
                                      l₂ ← elabEMode loc'
                                      guardErr (eq_mode m l₂) $
                                        typeError "synWRite: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
                                          [ ("m", pretty m), ("l", pretty l₂)]
                                      return τ
            _ →  typeError "synWrite: ; e not a string" (frhs [("e", pretty e₂)])
      _ →  typeError "synWrite: ; e not a basetype" (frhs [("e", pretty e₁)])


-------------------
--- Type Annotations ---
-------------------

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
      -- Writes are also read only
      (SecT loc (RefT _ τ'))  → do
        m  ← askL terModeL
        l ← elabEMode loc
        --  dont need subcond  ←  (subtype_embed τ (SecT m (RefT t')))
        guardErr (eq_mode m l) $
          typeError "synRefRead: m /≡ l" $ frhs
          [ ("m", pretty m)
          , ("l", pretty l)
          ]
        return τ'
      _  → typeError "synRefRead: τ is not a located reference" $ frhs
          [ ("τ", pretty τ)

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
        guardErr ((eq_mode m l₁₁) ⩓ (eq_mode m l₁₂)) $
          typeError "synRefWrite: m /≡ l₁₁ or  m /≡ l₁₂" $ frhs
          [ ("m", pretty m)
          , ("l₁₁", pretty l₁₁)
          , ("l₁₂", pretty l₁₂)
          ]
        (ty_join  τ₁' τ₂)

      _ → typeError "synRefWrite: τ₁ is not a located reference" $ frhs
           [ ("τ₁", pretty τ₁)]

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
      (SecT loc (BaseT (ℕT _)))  → do
        m  ← askL terModeL
        l ← elabEMode loc
        em ← elabMode m
        guardErr (eq_mode m l) $
          typeError "synArray: m /≡ l" $ frhs
          [ ("m", pretty m)
          , ("l", pretty l)
          ]
        return $ SecT em (ArrT (Some em) τ₂)
      _  →  typeError "synArray: τ₁ is not a located natural number" $ frhs
              [ ("τ₁", pretty τ₁)]


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
        --  dont need subcond  ←  (subtype_embed τ (SecT m (RefT t')))
        guardErr (eq_mode m l₁) $
          typeError "synArrayRead: m /≡ l₁" $ frhs
          [ ("m", pretty m)
          , ("l₁", pretty l₁)
          ]

        case τ₂ of
          (SecT loc₂ (BaseT (ℕT _)))  → do
            l₂ ← elabEMode loc₂
            em ← elabMode m
            guardErr (eq_mode m l₂) $
              typeError "synArray: m /≡ l" $ frhs
              [ ("m", pretty m)
                , ("l₂", pretty l₂)
              ]
            return τ₁'
          _  →  typeError "synArrayRead: τ₂ is not a located natural number" $ frhs
              [ ("τ₂", pretty τ₂)]
      _  →  typeError "synArrayRead: τ₁ is not a located array" $ frhs
          [ ("τ₁", pretty τ₁)

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
        --  dont need subcond  ←  (subtype_embed τ (SecT m (ArrT _ t')))
        guardErr ((eq_mode m l₁₁) ⩓ (eq_mode m l₁₂)) $
          typeError "synRefWrite: m /≡ l₁₁ or  m /≡ l₁₂" $ frhs
          [ ("m", pretty m)
          , ("l₁₁", pretty l₁₁)
          , ("l₁₂", pretty l₁₂)
          ]
        case τ₂ of
          (SecT loc₂ (BaseT (ℕT _)))  → do
            l₂ ← elabEMode loc₂
            em ← elabMode m
            guardErr (eq_mode m l₂) $
              typeError "synArrayWrite: m /≡ l₂" $ frhs
                [ ("m", pretty m)
                  , ("l₂", pretty l₂)
                ]
            (ty_join  τ₁' τ₃)
          _  → typeError "synRefRead: τ₂ is not a located natural number" $ frhs
                [ ("τ₂", pretty τ₂ )]
      _  →  typeError "synArrayRead: τ₁ is not a located array" $ frhs
          [ ("τ₁", pretty τ₁)

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
      SecT loc (ArrT _ τ')  → do
          m  ← askL terModeL
          l ← elabEMode loc
          em ← elabMode m
          --  dont need subcond  ←  (subtype_embed τ (SecT m (RefT t')))
          guardErr (eq_mode m l) $
            typeError "synArraySize: m /≡ l" $ frhs
            [ ("m", pretty m)
            , ("l", pretty l)
            ]
          return (SecT em (BaseT (ℕT iprDefault)))
      _ →  typeError "synArrayRead: τ is not a located array" $ frhs
          [ ("τ", pretty τ)

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
    t₁ ← c₁
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

checkPar ∷ STACK ⇒  PrinSetExp → Exp → Type → EM ()
checkPar ρse₁ e₂ τ=
  let c₁ = synPrinSet ρse₁
      c₂ = synExp e₂
  in do
    t₁ ← c₁
    m  ← askL terModeL
    l ← elabEMode (AddTop ρse₁)
    let m' = inter_m m l
    if m' ≢  (AddAny (AddTop bot)) then do
      τ' ← localL terModeL m' c₂
      subcond  ← subtype_embed τ' τ pø
      guardErr subcond $
        typeError "checkPar: τ' is not a subtype of τ" $ frhs
          [ ("τ'", pretty τ')
          , ("τ", pretty τ)
          ]
      return ()
    else do
      bigM ← askL terModeScopeL
      wfcond ← (wf_type τ  (AddAny (AddTop pø)) bigM)
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
        t₁ ← c₁
        t₂ ← c₂
        m  ← askL terModeL
        -- Literally this line is the only line that needs to change
        p ←  elabEMode (AddTop (ρse₁))
        qs ← elabPrinSetExp ρse₂
        q ←  elabEMode (AddTop ρse₂)
        _ <-  case qs of
              (Inl qs) → do
                          guardErr (not (isEmpty  qs)) $
                            typeError "synShare: q is empty" $ frhs
                              [  ("q", pretty qs)
                              ]
                          return ()
              _  → return ()

              -- And this line
        cleartextτ ← (makeCleartextType (AddTop ρse₁) τ False)
      --  wfcond ← wf_type cleartextτ m
        subcond  ←  localL terModeL m (chkExp e₃ cleartextτ)
        guardErr (eq_mode (union_m p q)  m ) $
          typeError "synShare: p union q /= m" $ frhs
            [
              ("p", pretty p)
              , ("q", pretty q)
              , ("puq", pretty (union_m p q))
              , ("m", pretty m)
            ]

        (makeEncryptedType (AddTop ρse₂) φ τ True)

---  |-m e : encrypted by p type @p
--  q != empty set since it is a principal and p union q = m
-- ------T-Share
-- gamma |- m share[p -> q] e : cleartext type@ q
synReveal ∷ STACK ⇒ Prot → Type → PrinSetExp → PrinSetExp → Exp → EM Type
synReveal φ τ ρse₁ ρse₂ e₃ =
  let c₁ = synPrinSet ρse₁
      c₂ = synPrinSet ρse₂
      in do
        t₁ ← c₁
        t₂ ← c₂
        m  ← askL terModeL
        p ←  elabEMode (AddTop ρse₁)
        q ←  elabEMode (AddTop ρse₂)
        encryptedτ ← (makeEncryptedType (AddTop ρse₁) φ τ False)
        subcond  ←  localL terModeL m (chkExp e₃ encryptedτ)
        guardErr (eq_mode (union_m p q)  m ) $
          typeError "synReveal: p union q /= m" $ frhs
            [
              ("p", pretty p)
              , ("q", pretty q)
              , ("puq", pretty (union_m p q))
              , ("m", pretty m)
            ]

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
        t₁ ← c₁
        t₂ ← c₂
        m  ← askL terModeL
        -- Literally this line is the only line that needs to change
        p ←  elabEMode (AddTop ρse₁)
        qs ← elabPrinSetExp ρse₂
        q ←  elabEMode (AddTop ρse₂)
        _ <-  case qs of
                (Inl qs) → do
                            guardErr (not (isEmpty  qs)) $
                              typeError "syncOMM: q is empty" $ frhs
                              [ ("q", pretty qs)
                              ]
                            return ()
                _  → return ()

              -- And this line
        cleartextτ ← (makeCleartextType (AddTop ρse₁) τ False)
      --  wfcond ← wf_type cleartextτ m
        subcond  ←  localL terModeL m (chkExp e₃ cleartextτ)
        guardErr (eq_mode (union_m p q)  m ) $
          typeError "synComm: p union q /= m" $ frhs
            [
              ("p", pretty p)
              , ("q", pretty q)
              , ("puq", pretty (union_m p q))
              , ("m", pretty m)
            ]
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
                subcond  ← (subtype_embed τ₁ (SecT em (BaseT 𝔹T)) pø  )
                guardErr subcond $
                  typeError "synMuxIf: τ₁ is not a shared boolean" $ frhs
                    [  ("τ₁", pretty τ₁)
                    ]
                (ty_join τ₂ τ₃)
        else
          case ps  of
            ((p, loc) :& _) → do
              guardErr (and (map (\(p', l) -> (p ≡ p') ⩓  (eq_mode l m)) ps)) $
                typeError "synMuxIf: Not all protocols/encryptions are the same as p#loc" $ frhs
                  [ ("ρ", pretty p)
                  , ("loc'", pretty m)
                  ]
              eτs ← (mapM (embedShare p em) τs )
              case eτs of
                (τ₁ :& (τ₂ :& (τ₃ :& Nil))) → do
                  subcond  ← (subtype_embed τ₁ (SecT em (ShareT p em (BaseT 𝔹T))) pø  )
                  guardErr subcond $
                    typeError "synMuxIf: τ₁ is not a shared boolean" $ frhs
                    [  ("τ₁", pretty τ₁)]
                  (ty_join τ₂ τ₃)

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
    em ← elabMode m
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
                ((p, loc) :& _) → do
                  guardErr (and (map (\(p', l) -> (p ≡ p') ⩓  (eq_mode l m)) ps)) $
                    typeError "synMuxCase: Not all protocols/encryptions are the same as p#loc" $ frhs
                      [ ("ρ", pretty p)
                      , ("loc'", pretty m)
                      ]
                  eτs' ← (mapM (embedShare p em) τs' )
                  (joinList eτs')
            _ → typeError "synMuxCase: The first expression e of type τ is cleartext while the some of all of the bodies is not" $ frhs
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
            typeError "synBundleIntro: p /≡ p'" $ frhs
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
      _ → todoError

synBundleAccess ∷ STACK ⇒ Exp → PrinExp → EM Type
synBundleAccess e₁ ρe₂ =
  let c₁ = synExp e₁
      c₂ = synPrinExp ρe₂
  in do
    τ₁ ← c₁
    τ₂ ← c₂
    guardErr (isEmbedable τ₁) $
      typeError "synBundleAccess: τ₁ is not a common cleartext type'" $ frhs
      [ ("τ₁", pretty τ₁)
      ]
    case τ₁ of
      (SecT loc₁ (ISecT loc₁' τ₁'))  → do
        m  ← askL terModeL
        l₁ ← elabEMode loc₁
        --  dont need subcond  ←  (subtype_embed τ (SecT m (RefT t')))
        guardErr (eq_mode m l₁) $
          typeError "synBundleAccess: m /≡ l" $ frhs
          [ ("m", pretty m)
          , ("l", pretty l₁)
          ]
        do
          q ← elabEMode loc₁'
          p ←  elabEMode (AddTop (PowPSE (frhs [ρe₂])))
          guardErr (supermode q p)  $
            typeError "synBundleAccess: not p <= q" $ frhs
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
        guardErr (isEmbedable τ₁) $
          typeError "synBundleAccess: τ₁' is not a common cleartext type'" $ frhs
            [ ("τ₁'", pretty τ₁')
            ]
        m  ← askL terModeL
        l₁ ← elabEMode loc₁
        --  dont need subcond  ←  (subtype_embed τ (SecT m (RefT t')))
        guardErr (m ≡ l₁) $
          typeError "synBundle: m /≡ l" $ frhs
          [ ("m", pretty m)
          , ("l", pretty l₁)
          ]
        case τ₂ of
          (SecT loc₂ (ISecT loc₂' τ₂'))  → do
            l₂ ← elabEMode loc₂
            em ← elabMode m
            guardErr (m ≡ l₂) $
              typeError "synBundle: m /≡ l" $ frhs
              [ ("m", pretty m)
                , ("l", pretty l₂)
              ]
            p₁ ← elabEMode loc₁'
            p₂ ← elabEMode loc₂'
            guardErr (inter_m p₁ p₂ ≡ (AddAny (AddTop bot))) $
              typeError "synBundle: p₁ ⊓ p₂ ≢  bot" $ frhs
              [ ("p₁", pretty p₁)
                , ("p₂", pretty p₂)
              ]
            q ← elabMode (union_m p₁ p₂)
            τ ←  (locty_join τ₁' τ₂')
            return  (SecT loc₂ (ISecT q τ))
        
      _ →           typeError "synBundleAccess: τ₁ is not a bundle type'" $ frhs
              [ ("τ₁", pretty τ₁)
              ]

-------------------
--- Recursive Types ---
-------------------

-- u = (mu alpha. t)
-- gamma |- m e : [(mu alpha. t)/ alpha] t
-- ------T-Fold
-- gamma |- fold [u] x : u
checkFold ∷ STACK ⇒ Exp → Type → EM ()
checkFold e τ=
 case τ of
    (RecT a τ')   →  do
      substtype ←  type_subst a τ' τ
      _  ← chkExp e substtype
      return ()
    _  → typeError "checkFold: Type is given is not a recursive type" $ frhs [ ("τ'", pretty τ)]


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
      _  → typeError "synUnfold: Type given is not a recursive type" $ frhs [ ("τ'", pretty τ)]

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
      _ → typeError " e has type τ' which is not a forall type " $ frhs
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
      LE eₗ        → checkL eₗ τ
      RE eᵣ        → checkR eᵣ τ
      NilE        → checkNil τ
      LamE self𝑂 ψs e → checkLam self𝑂 ψs e τ
      ParE ρse₁ e₂ → checkPar ρse₁ e₂ τ
      FoldE e → checkFold e τ
      --UnfoldE e → synUnfold e
      _ →
          do
            τ' ← synExpR e
            subcond  ← (subtype_embed τ' τ pø)
            guardErr subcond $
              typeError "checkExpR: e has type τ' which is not a subtype of τ" $ frhs
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
  BoolE b     → synBool b
  NatE pr n   → synNat pr n
  IntE pr z   → synInt pr z
  FltE pr d   → synFlt pr d
  StrE s      → synStr s
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

asTLM ∷ STACK ⇒ EM a → TLM a
asTLM eM = do
  γ ← getL ttlsEnvL
  ps ← getL ttlsPrinsL
  let r = ER { terSource = None, terMode = (AddAny Top), terEnv = γ, terModeScope = dø, terPrins = ps }
  evalEMErr r () eM

bindTypeTL ∷ STACK ⇒ 𝕏 → Type → TLM ()
bindTypeTL x τ = do
  asTLM $ (wf_typeTL τ)
  modifyL ttlsEnvL ((x ↦ τ) ⩌)

wf_typeTL ∷ STACK ⇒ Type → EM ()
wf_typeTL τ =
  case τ of
    SecT loc (τ₁₁ :→: (η :* τ₁₂))   →
                  do
                    l₁ ← elabEMode $ effectMode η
                    l₂ ← elabEMode loc
                    guardErr (eq_mode l₁ l₂) $
                      typeError " WFCheckTL: ⊢ₘ _ ˡ→ _ ; m ≢ l₂ in τ" $ frhs
                      [ ("l₁", pretty l₂)
                      , ("l₂", pretty l₂)
                      , ("τ", pretty τ)
                      ]
                    (wf_type τ l₁ dø)
    _ →  (wf_type τ Any dø)
