module Symphony.TypeChecker where

import UVMHS
import AddToUVMHS

import Symphony.Syntax
import Symphony.TypeChecker.Error
import Symphony.TypeChecker.TLM hiding (TLR)
import Symphony.TypeChecker.EM
import Symphony.TypeChecker.Operations

---------------------
-- Checking for TL --
---------------------

synProg ∷ 𝐿 TL → TLM Type
synProg prog = do
  eachOn prog bindTL
  asTLM $ do
    τMain ← synVar $ var "main"
    synAppTL τMain $ BaseT UnitT

bindTL ∷ TL → TLM ()
bindTL tl = localL ttlrSourceL (Some $ atag tl) $ bindTLR $ extract tl

bindTLR ∷ TLR → TLM ()
bindTLR tlr = case tlr of
  DeclTL _brec x τ    → bindDecl x τ
  DefnTL _brec x ψs e → bindDefn x ψs e
  PrinTL ρds          → bindPrins ρds
  ImportTL path       → todoError

bindDecl ∷ 𝕏 → Type → TLM ()
bindDecl = bindTypeTL

bindDefn ∷ 𝕏 → 𝐿 Pat → Exp → TLM ()
bindDefn x ψs e = asTLM $ do
  τ ← synVar x
  chkLam (Some x) ψs e τ

bindPrins ∷ 𝐿 PrinDecl → TLM ()
bindPrins ρds = eachOn ρds bindPrin
  where bindPrin ρd = case ρd of
          SinglePD ρ   → bindTypeTL (var ρ) $ BaseT ℙT
          ArrayPD ρ _n → bindTypeTL (var ρ) $ BaseT ℙsT

chkLam ∷ 𝑂 Var → 𝐿 Pat → Exp → Type → EM ()
chkLam self𝑂 ψs e τ = todoError

synAppTL ∷ Type → Type → EM Type
synAppTL τ₁ τ₂ = case τ₁ of
  SecT loc (τ₁₁ :→: (η :* τ₁₂)) → do
    m  ← askL terModeL
    l₁ ← elabEMode $ effectMode η
    l₂ ← elabEMode loc
    guardErr (m ≡ l₁) $
      typeError "synApp: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
      [ ("m", pretty m)
      , ("l", pretty l₁)
      ]
    return τ₂
  _ → typeError "synApp: τ₁ ≢ (_ → _)@_" $ frhs
      [ ("τ₁", pretty τ₁)
      ]
------------------------------
-- Checking for Expressions --
------------------------------

-- ------ T-Var
synVar ∷ Var → EM Type
synVar x = do
  env ← askL terEnvL
  case env ⋕? x of
    Some τ → do
      m ← askL terModeL
      -- T-Var: gets the well formed supertype if there is one, if not error
      (superty_wf τ m)
    None   → typeError "synVar: x ∉ Γ" $ frhs
             [ ("x", pretty x)
             , ("Γ", pretty $ keys env)
             ]


------------------
--- Primitives ---
------------------

-- ------ T-Bul
-- gamma |- m () : bul@m
synBul ∷ EM Type
synBul =  do
  m ← askL terModeL
  em ← elabMode m
  return (SecT em (BaseT UnitT))

-- ------ T-Bool
-- gamma |- m b : bool@m
synBool ∷ 𝔹 → EM Type
synBool b =  do
  m ← askL terModeL
  em ← elabMode m
  return (SecT em (BaseT 𝔹T))

-- ------ T-Nat
-- gamma |- m n : nat@m
synNat ∷ IPrecision → ℕ → EM Type
synNat pr n = do
  m ← askL terModeL
  em ← elabMode m
  return (SecT em (BaseT (ℕT pr)))

-- ------ T-Int
-- gamma |- m i : int@m
synInt ∷ IPrecision → ℤ → EM Type
synInt pr z = do
  m ← askL terModeL
  em ← elabMode m
  return (SecT em (BaseT (ℤT pr)))

-- ------ T-Float
-- gamma |- m d : float@m
synFlt ∷ FPrecision → 𝔻 → EM Type
synFlt pr d = do
  m ← askL terModeL
  em ← elabMode m
  return (SecT em (BaseT (𝔽T pr)))

-- ------ T-String
-- gamma |- m s : string@m
synStr ∷  𝕊 → EM Type
synStr s = do
  m ← askL terModeL
  em ← elabMode m
  return (SecT em (BaseT 𝕊T))

-- gamma(x) = t
-- ------ T-PrinExp
-- gamma |- m b : t
synPrinExp ∷ PrinExp → EM Type
synPrinExp ρe = case ρe of
  VarPE x       → synVar x
  AccessPE x n₁ → synVar x


-- forall A in M = {A ...} gamma |- m A t t <: prin@all
checkPrin ∷ PrinExp → EM Type
checkPrin ρe =
   do
    ρτ ← (synPrinExp ρe) 
    subcond ← (subtype (SecT Top (BaseT ℙT)) ρτ)
    case subcond of
      True → return (SecT Top (BaseT ℙT))
      False → todoError

-- forall A in M = {A ...} gamma |- m A t t <: prin@all   
-- ------T-PrinSetExp
-- gamma |- m A : ps@all
synPrinSet ∷ PrinSetExp → EM Type
synPrinSet ρse =
  case ρse of
  PowPSE ρes → do
    _ ←  mapM checkPrin ρes
    m ← askL terModeL
    em ← elabMode m
    return (SecT em (BaseT ℙsT))
  _    →  todoError

synPrim ∷ Op → 𝐿 Exp → EM Type
synPrim op es =
  if (isEmpty es) then
     do 
       m ← askL terModeL
       em ← elabMode m
       bt ← (primType op (empty𝐿 ))
       return (SecT em (BaseT bt))
  else
    do 
      m ← askL terModeL
      em ← elabMode m
      τs ← (mapM synExp es)
      _ ← (mapM (assertM m) τs)
      pos ← (mapM extractProt τs)
      bs ← (mapM extractBase τs)
      bt ← (primType op bs)
      let ps = list𝐼 (filterMap (\x -> x)  pos) in
        if (isEmpty ps) then 
          return (SecT em (BaseT bt))
        else
          case ps  of
            ((p, loc) :& _) → 
              if (and (map (\(p', l) -> (p == p') ⩓  (l == m)) ps)) then
                return (SecT em (ShareT p em (BaseT bt))) 
              else
                todoError
    
     
---------------------------------
--- Products, Sums, and Lists ---
---------------------------------

--Gets the type of the first, gets type of the second, returns the pair located value
synProd ∷  Exp → Exp → EM Type
synProd eₗ eᵣ =
  let cₗ = synExp eₗ
      cᵣ = synExp eᵣ
  in do
    τₗ ← cₗ
    τᵣ ← cᵣ
    m ← askL terModeL
    em ← elabMode m
    return (SecT em (τₗ :×: τᵣ))


checkL ∷ Exp → Type → EM ()
checkL eₗ τ  =
  case τ of
    (SecT em (τₗ  :+: τᵣ)) →
      let cₗ = synExp eₗ
      in do
        cτₗ  ← cₗ
        subcond  ← (subtype cτₗ τₗ)
        (if subcond then return () else todoError)
    x → todoError

checkR ∷ Exp → Type → EM ()
checkR eᵣ τ  =
  case τ of
    (SecT em (τₗ  :+: τᵣ)) →
      let cᵣ = synExp eᵣ
      in do
        cτᵣ  ← cᵣ
        subcond  ← (subtype cτᵣ τᵣ)
        m  ← askL terModeL
        if subcond then
          return ()
        else
          todoError
    x → todoError

{- Todo: Check if m is a subset of the real mode-}
checkNil ∷ Type → EM ()
checkNil τ =  
  case τ of
    SecT m (ListT _ τₜ)  → return ()
    x  → todoError

synCons ∷ Exp → Exp → EM Type
synCons eₕ eₜ =
  let cₕ = synExp eₕ
      cₜ = synExp eₜ
  in do
    τ  ← cₕ
    τs ← cₜ
    case τs of
      SecT em' (ListT n τₜ)  →  do
        m ← askL terModeL
        em ← elabMode m 
        join_t ← (ty_join τ  τₜ)
        em'' ← (inter_em em' em)
        return (SecT em'' (ListT n join_t))

synIf :: Exp → Exp → Exp → EM Type
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
    subcond ← (subtype τ₁ (SecT em (BaseT 𝔹T)) )
    if subcond then do
      (ty_join τ₂ τ₃)
    else
      todoError

synCase ∷ Exp → 𝐿 (Pat ∧ Exp) → EM Type
synCase e ψes =
  let c = synExp e
  in do
    τ  ← c
    case τ of
      (SecT loc (ShareT _ _ _)) → todoError
      (SecT loc _) → do
        m ← askL terModeL
        l ← elabEMode loc
        guardErr (m ≡ l) $
          typeError "synCase: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
          [ ("m", pretty m)
          , ("l", pretty l)
          ]
        τs ← mapM (synBind τ) ψes
        (joinList τs)

synBind ∷ Type → (Pat ∧ Exp) → EM Type 
synBind τ₁ (ψ :* e₂) =
  let c₂ = synExp e₂
  in do
    f  ← bindType τ₁ ψ
    f c₂
-----------------
--- Functions ---
-----------------

synLet ∷ Pat → Exp → Exp → EM Type 
synLet ψ e₁ e₂ =
  let c₁ = synExp e₁
  in do
    τ₁ ← c₁
    synBind τ₁ (ψ :* e₂)


-- type is well formed
checkLam ∷ 𝑂 Var → 𝐿 Pat → Exp →  Type → EM ()
checkLam self𝑂 ψs e τ = 
  case τ of
    SecT loc (τ₁₁ :→: (η :* τ₁₂))   → 
      case self𝑂 of
      None      →  
                  do
                    m  ← askL terModeL
                    l₂ ← elabEMode loc
                    guardErr (m ≡ l₂) $
                      typeError "synLam: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
                      [ ("m", pretty m),
                        ("l", pretty l₂)
                      ]
                    case ψs of
                      Nil → do
                        τ₁₂' ← (synExp e)
                        subcond  ← (subtype τ₁₂' τ₁₂)
                        if subcond then
                          return ()
                        else
                          todoError
                      ψ :& Nil → do
                        bind ←  (bindType τ₁₁ ψ) 
                        bind (chkExp e τ₁₂)
                      ψ :& ψs → do
                        bind ←  (bindType τ₁₁ ψ) 
                        bind (checkLam None ψs e τ₁₂)
  
                    
      Some self → (bindTo self τ) (checkLam None ψs e τ)
    x  → todoError
  
synApp ∷ Exp → Exp → EM Type
synApp e₁ e₂ = 
  let c₁ = synExp e₁
      c₂ = synExp e₂
  in do
    τ₁ ← c₁
    τ₂ ← c₂
    case τ₁ of
      SecT loc (τ₁₁ :→: (η :* τ₁₂)) → do
        m  ← askL terModeL
        l₁ ← elabEMode $ effectMode η
        l₂ ← elabEMode loc
        subcond  ←  (subtype τ₂ τ₁₂)
        guardErr (m ≡ l₁) $
          typeError "synApp: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
          [ ("m", pretty m)
          , ("l", pretty l₁)
          ]
        guardErr (m ≡ l₂) $
          typeError "synApp: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
          [ ("m", pretty m)
          , ("l", pretty l₁)
          ]
        return τ₂
      _ → typeError "synApp: τ₁ ≢ (_ → _)@_" $ frhs
          [ ("τ₁", pretty τ₁)
          ]

----------------------
--- Read and Write ---
----------------------

synRead ∷ Type → Exp → EM Type
synRead τ e =
  let c = synExp e
  in do
    m ← askL terModeL
    wfcond ← (wf_type τ m)
    τ' ← c
    guardErr ((map psize m) == (AddTop 1)) $
      typeError "synRead: ⊢ₘ ; |m| ≢  1" $ frhs
      [ ("m", pretty m)
      ]
    case τ' of
      (SecT loc (BaseT 𝕊T))  →  
        do
          l ← elabEMode loc
          guardErr (m ≡ l) $
            typeError "synRead: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
                , ("l", pretty l)
              ]
          return τ
      _ →  typeError "synRead: ; e not a string" (frhs [("e", pretty e)])
   


synWrite ∷  Exp → Exp → EM Type
synWrite e₁ e₂ =
  let c₁ = synExp e₁
      c₂ = synExp e₂
  in do
    m ← askL terModeL
    τ ← c₁
    τ' ← c₂
    guardErr ((map psize m) == (AddTop 1)) $
      typeError "synWrite: ⊢ₘ ; |m| ≢  1" $ frhs
      [ ("m", pretty m)
      ]
    case τ of
      (SecT loc bτ)  → do
          l₁ ← elabEMode loc
          guardErr (m ≡ l₁) $
            typeError "synWRite: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
                , ("l", pretty l₁)
              ]
          case τ' of
            (SecT loc' (BaseT 𝕊T))  → do
                                      l₂ ← elabEMode loc'
                                      guardErr (m ≡ l₂) $
                                        typeError "synWRite: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
                                          [ ("m", pretty m), ("l", pretty l₂)]
                                      return τ
            _ →  typeError "synWrite: ; e not a string" (frhs [("e", pretty e₂)])
      _ →  typeError "synWrite: ; e not a basetype" (frhs [("e", pretty e₁)])
    

-------------------
--- Type Annotations ---
-------------------

synAscr :: Exp → Type →  EM Type
synAscr e τ = do 
  _ ← (chkExp e τ)
  return τ

-------------------
--- References ---
-------------------

synRef ∷ Exp → EM Type
synRef e =
  let c = synExp e
  in do
  τ ← c
  m  ← askL terModeL
  em ← elabMode m
  return (SecT em (RefT (Some em) τ))

synRefRead ∷ Exp → EM Type
synRefRead e =
  let c = synExp e
  in do
    τ ← c
    case τ of
      -- None is subtype
      (SecT loc (RefT _ τ'))  → do
        m  ← askL terModeL
        l ← elabEMode loc
        --  dont need subcond  ←  (subtype τ (SecT m (RefT t')))
        guardErr (m ≡ l) $
          typeError "synRefRead: m /≡ l" $ frhs
          [ ("m", pretty m)
          , ("l", pretty l)
          ]
        return τ'
      _  → todoError



synRefWrite ∷ Exp → Exp → EM Type
synRefWrite e₁ e₂ =
  let c₁ = synExp e₁
      c₂ = synExp e₂
  in do
    τ₁  ← c₁
    τ₂ ← c₂
    case τ₁ of
      (SecT loc₁ (RefT (Some loc₂) τ₁'))  → do  
        m  ← askL terModeL
        l₁ ← elabEMode loc₁
        l₂ ← elabEMode loc₂
        guardErr ((m ≡ l₁) ⩓ (m ≡ l₂)) $
          typeError "synRefRead: m /≡ l" $ frhs
          [ ("m", pretty m)
          , ("l", pretty l₁)
          ] 
        (ty_join  τ₁' τ₂)
        
      _ → todoError

synArray ∷ Exp → Exp → EM Type
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
        guardErr (m ≡ l) $
          typeError "synArray: m /≡ l" $ frhs
          [ ("m", pretty m)
          , ("l", pretty l)
          ]
        return (SecT em (ArrT (Some em) 0 τ₂))

synArrayRead ∷ Exp → Exp → EM Type
synArrayRead e₁ e₂ =
  let c₁ = synExp e₁
      c₂ = synExp e₂
  in do
    τ₁ ← c₁
    τ₂ ← c₂
    case τ₁ of
      (SecT loc₁ (ArrT _ _ τ₁'))  → do
        m  ← askL terModeL
        l₁ ← elabEMode loc₁
        --  dont need subcond  ←  (subtype τ (SecT m (RefT t')))
        guardErr (m ≡ l₁) $
          typeError "synArrayRead: m /≡ l" $ frhs
          [ ("m", pretty m)
          , ("l", pretty l₁)
          ]
        case τ₂ of
          (SecT loc₂ (BaseT (ℕT _)))  → do
            l₂ ← elabEMode loc₂
            em ← elabMode m
            guardErr (m ≡ l₂) $
              typeError "synArray: m /≡ l" $ frhs
              [ ("m", pretty m)
                , ("l", pretty l₂)
              ]
            return τ₁'
          _  → todoError
      _  → todoError


synArrayWrite ∷ Exp → Exp → Exp → EM Type
synArrayWrite e₁ e₂ e₃ =
  let c₁ = synExp e₁
      c₂ = synExp e₂
      c₃ = synExp e₃
  in do
    τ₁ ← c₁
    τ₂ ← c₂
    τ₃ ← c₃
    case τ₁ of
      (SecT loc₁ (ArrT (Some loc₂) _ τ₁'))  → do
        m  ← askL terModeL
        l₁ ← elabEMode loc₁
        l₂ ← elabEMode loc₂
        --  dont need subcond  ←  (subtype τ (SecT m (RefT t')))
        guardErr ((m ≡ l₁) ⩓ (m ≡ l₂)) $
          typeError "synArrayWrite: m /≡ l" $ frhs
          [ ("m", pretty m)
          , ("l", pretty l₁)
          ]
        case τ₂ of
          (SecT loc₂ (BaseT (ℕT _)))  → do
            l₂ ← elabEMode loc₂
            em ← elabMode m
            guardErr (m ≡ l₂) $
              typeError "synArrayWrite: m /≡ l" $ frhs
                [ ("m", pretty m)
                  , ("l", pretty l₂)
                ]
            (ty_join  τ₁' τ₃)
          _  → todoError
      _  → todoError

synArraySize ∷ Exp → EM Type
synArraySize e =
  let c = synExp e 
  in do
    τ ← c
    case τ of
      SecT loc (ArrT _ _ τ')  → do
          m  ← askL terModeL
          l ← elabEMode loc
          em ← elabMode m
          --  dont need subcond  ←  (subtype τ (SecT m (RefT t')))
          guardErr (m ≡ l) $
            typeError "synArraySize: m /≡ l" $ frhs
            [ ("m", pretty m)
            , ("l", pretty l)
            ]
          return (SecT em (BaseT (ℕT InfIPr)))
      _ → todoError


-----------
--- Par ---
-----------

synPar ∷  PrinSetExp → Exp → EM Type
synPar ρse₁ e₂ =
  let c₁ = synPrinSet ρse₁
      c₂ = synExp e₂
  in do
    m  ← askL terModeL
    ρ𝑃 ← (elabPrinSetExp  ρse₁)
    let l = AddTop ρ𝑃
    let m' = m ⊓ l
    if m' ≢ bot then
      localL terModeL m' c₂
    else
      return (SecT (AddTop (PowPSE empty𝐿)) (BaseT UnitT))

checkPar ∷  PrinSetExp → Exp → Type → EM ()
checkPar ρse₁ e₂ τ=
  let c₁ = synPrinSet ρse₁
      c₂ = synExp e₂
  in do
    m  ← askL terModeL
    ρ𝑃 ← (elabPrinSetExp  ρse₁)
    let l = AddTop ρ𝑃
    let m' = m ⊓ l
    if m' ≢ bot then do 
      τ' ← localL terModeL m' c₂
      subcond  ← (subtype τ' τ)
      if subcond then
              return ()
      else
        todoError
    else do
      wfcond ← (wf_type τ  (AddTop pø))
      return ()


synShare ∷  Prot → Type → PrinExp → PrinSetExp → Exp → EM Type
synShare φ τ ρe₁ ρse₂ e₃ =
  let c₁ = synPrinExp ρe₁
      c₂ = synPrinSet ρse₂
      in case τ of
        SecT loc' τ' → do

            m  ← askL terModeL
            p ←  elabEMode (AddTop (PowPSE (frhs [ρe₁])))
            p' ← elabEMode loc'
            qs ← elabPrinSetExp ρse₂
            --wfcond ← wf_type (SecT (AddTop ρse₂) (ShareT φ (AddTop ρse₂) τ') ) (AddTop qs)
            subcond  ←  localL terModeL m (chkExp e₃ τ)
            if (not (isEmpty  qs)) ⩓ (supermode p' p) 
              then return (SecT (AddTop ρse₂) (ShareT φ (AddTop ρse₂) τ') ) 
              else todoError
        _ → do
          todoError

-- Assume φ is in type
synReveal ∷ Prot → Type → PrinSetExp → PrinExp → Exp → EM Type
synReveal φ τ ρse₁ ρe₂ e₃ =
  let c₁ = synPrinSet ρse₁
      c₂ = synPrinExp ρe₂
      in case τ of
        SecT loc (ShareT φ loc' τ') → do            
            m  ← askL terModeL
            p ←  elabEMode loc
            p' ← elabEMode loc'
            qs ← elabPrinSetExp  (PowPSE (frhs [ρe₂]))
            subcond  ←  localL terModeL m (chkExp e₃ τ)
            if (not (isEmpty  qs)) ⩓ (p ≡ p') ⩓ (m ≡ ( p ⊓ (AddTop qs)) )
              then return (SecT (AddTop (PowPSE (frhs [ρe₂]))) τ' ) 
              else todoError
        _ → do
          todoError

synComm ∷  Type → PrinExp → PrinSetExp → Exp → EM Type
synComm τ ρe₁ ρse₂ e₃ =
  let c₁ = synPrinExp ρe₁
      c₂ = synPrinSet ρse₂
      in case τ of
        SecT loc' τ' → do
            m  ← askL terModeL
            p ←  elabEMode (AddTop (PowPSE (frhs [ρe₁])))
            p' ← elabEMode loc'
            qs ← elabPrinSetExp ρse₂
            subcond  ←  localL terModeL m (chkExp e₃ τ)
            if (not (isEmpty  qs)) ⩓ (supermode p' p) 
              then return (SecT (AddTop ρse₂) τ' ) 
              else todoError
        _ → do
          todoError

synMuxIf ∷  Exp → Exp → Exp → EM Type
synMuxIf e₁ e₂ e₃ =do 
      m ← askL terModeL
      em ← elabMode m
      τs ← (mapM synExp (frhs [e₁, e₂, e₃]) )
      _ ← (mapM (assertM m) τs)
      pos ← (mapM extractProt τs)
      let ps = list𝐼 (filterMap (\x -> x)  pos) in
        if (isEmpty ps) then 
          do
            case τs of
                    (τ₁ :& (τ₂ :& (τ₃ :& Nil))) → do
                      subcond  ← (subtype τ₁ (SecT em (BaseT 𝔹T)) )
                      if subcond then do
                        (ty_join τ₂ τ₃)
                      else
                        todoError
        else
          case ps  of
            ((p, loc) :& _) → 
              if (and (map (\(p', l) -> (p == p') ⩓  (l == m)) ps)) then
                do
                  eτs ← (mapM (embedShare p em) τs )
                  case eτs of
                    (τ₁ :& (τ₂ :& (τ₃ :& Nil))) → do
                      subcond  ← (subtype τ₁ (SecT em (ShareT p em (BaseT 𝔹T))) )
                      if subcond then do
                        (ty_join τ₂ τ₃)
                      else
                        todoError
              else
                todoError


synMuxCase ∷  Exp → 𝐿 (Pat ∧ Exp) → EM Type
synMuxCase e ψes =do 
  let c = synExp e in do
    τ  ← c

    m ← askL terModeL
    em ← elabMode m
    τs' ← mapM (synBind τ) ψes
    let τs = (τ :& τs') in do
      _ ← (mapM (assertM m) τs)
      pos ← (mapM extractProt τs)
      let ps = list𝐼 (filterMap (\x -> x)  pos) in
        if (isEmpty ps) then 
          (joinList τs')
        else
          case ps  of
            ((p, loc) :& _) → 
              if (and (map (\(p', l) -> (p == p') ⩓  (l == m)) ps)) then
                do
                  eτs' ← (mapM (embedShare p em) τs' )
                  (joinList eτs')
                    
              else
                todoError
    

-- Bundles
synBundleIntro :: (PrinExp ∧ Exp) → EM Type
synBundleIntro (pe :* e) = 
  let c = synExp e
  in do
    τ ← c
    _ ← assertShareable τ
    m  ← askL terModeL
    em ← elabMode m
    case τ of
      (SecT loc τ' ) → do
          p ←  elabEMode (AddTop (PowPSE (frhs [pe])))
          p' ← elabEMode loc
          guardErr (p ≡ p') $
            typeError "synBundleAccess: p /≡ p'" $ frhs
              [ ("p", pretty p)
              , ("p'", pretty p')
              ]
          return (SecT em (ISecT loc τ'))
      _ → todoError

synBundle ∷ 𝐿 (PrinExp ∧ Exp) → EM Type
synBundle ρee𝐿 =
  do
    τs ← (mapM synBundleIntro ρee𝐿)
    case τs of
      (τ :& τs') → (mfold τ synBundleUnionHelper τs)
      _ → todoError

synBundleAccess ∷ Exp → PrinExp → EM Type
synBundleAccess e₁ ρe₂ =
  let c₁ = synExp e₁
      c₂ = synPrinExp ρe₂
  in do
    τ₁ ← c₁
    τ₂ ← c₂
    case τ₁ of
      (SecT loc₁ (ISecT loc₁' τ₁'))  → do
        m  ← askL terModeL
        l₁ ← elabEMode loc₁
        --  dont need subcond  ←  (subtype τ (SecT m (RefT t')))
        guardErr (m ≡ l₁) $
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
      _  → todoError

synBundleUnion ∷ Exp → Exp → EM Type
synBundleUnion e₁ e₂ =
  let c₁ = synExp e₁
      c₂ = synExp e₂
  in do
    τ₁ ← c₁
    τ₂ ← c₂
    synBundleUnionHelper τ₁ τ₂


synBundleUnionHelper ∷ Type → Type → EM Type
synBundleUnionHelper τ₁ τ₂ =

    case τ₁ of
      (SecT loc₁ (ISecT loc₁' τ₁'))  → do
        m  ← askL terModeL
        l₁ ← elabEMode loc₁
        --  dont need subcond  ←  (subtype τ (SecT m (RefT t')))
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
            guardErr (p₁ ⊓ p₂ ≡ bot) $
              typeError "synBundle: p₁ ⊓ p₂ ≢  bot" $ frhs
              [ ("p₁", pretty p₁)
                , ("p₂", pretty p₂)
              ]
            q ← elabMode (p₁ ⊔ p₂)
            τ ←  (ty_join τ₁' τ₂')
            return  (SecT loc₂ (ISecT q τ))
            
-------------------
--- Expressions ---
-------------------

chkExp :: Exp → Type → EM ()
chkExp e τ = chkExpR (extract e) τ

chkExpR :: ExpR → Type → EM ()  
chkExpR e τ = 
  do 
    m  ← askL terModeL
    wfcond ← (wf_type τ m)
    case e of
      LE eₗ        → checkL eₗ τ
      RE eᵣ        → checkR eᵣ τ
      NilE        → checkNil τ
      LamE self𝑂 ψs e → checkLam self𝑂 ψs e τ
      ParE ρse₁ e₂ → checkPar ρse₁ e₂ τ
      _ →     
          do 
            τ' ← synExpR e
            subcond  ← (subtype τ' τ)
            if subcond then
              return ()
            else
              todoError


synExp :: Exp → EM Type
synExp e = synExpR $ extract e


synExpR ∷ ExpR → EM Type
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
  PrinE e → checkPrin e
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
  ShareE φ τ ρe₁ ρse₂ e₃  → synShare φ τ ρe₁ ρse₂ e₃
  RevealE φ τ ρse₁ ρe₂ e₃ → synReveal φ τ ρse₁ ρe₂ e₃
  SendE τ ρe₁ ρse₂ e₃     → synComm τ ρe₁ ρse₂ e₃

  -- MPC Operations
  MuxIfE e₁ e₂ e₃ → synMuxIf e₁ e₂ e₃
  MuxCaseE e ψes  → synMuxCase e ψes

  -- Bundles
  BundleE ρees         → synBundle ρees
  BundleAccessE e₁ ρe₂ → synBundleAccess e₁ ρe₂
  BundleUnionE e₁ e₂   → synBundleUnion e₁ e₂
  
  _      → undefined


---------------
-- Utilities --
---------------

asTLM ∷ EM a → TLM a
asTLM eM = do
  γ ← getL ttlsEnvL
  let r = ER { terSource = None, terMode = Top, terEnv = γ }
  evalEMErr r () eM

bindTypeTL ∷ 𝕏 → Type → TLM ()
bindTypeTL x τ = modifyL ttlsEnvL ((x ↦ τ) ⩌)

