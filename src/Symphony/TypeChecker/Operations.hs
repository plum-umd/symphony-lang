module Symphony.TypeChecker.Operations where

import UVMHS
import AddToUVMHS

import Symphony.Syntax
import Symphony.TypeChecker.Error
import Symphony.TypeChecker.TLM hiding (TLR)
import Symphony.TypeChecker.EM


-----------------
--- Primitives ---
-----------------

-- Takes an op, list of base types, and returns what the op should return on the base type 
primType ∷ Op → 𝐿 BaseType → EM BaseType
primType op τs = case (op, tohs τs) of
  (NotO,   [             𝔹T     ])             → return 𝔹T
  (AndO,   [     𝔹T,     𝔹T     ])             → return 𝔹T
  (PlusO,  [     ℤT pr₁, ℤT pr₂ ]) | pr₁ ≡ pr₂ → return $ ℤT pr₁
  (PlusO,  [     ℕT pr₁, ℕT pr₂ ]) | pr₁ ≡ pr₂ → return $ ℕT pr₁
  (MinusO, [     ℤT pr₁, ℤT pr₂ ]) | pr₁ ≡ pr₂ → return $ ℤT pr₁
  (TimesO, [     ℤT pr₁, ℤT pr₂ ]) | pr₁ ≡ pr₂ → return $ ℤT pr₁
  (DivO,   [     ℤT pr₁, ℤT pr₂ ]) | pr₁ ≡ pr₂ → return $ ℤT pr₁
  (ModO,   [     ℤT pr₁, ℤT pr₂ ]) | pr₁ ≡ pr₂ → return $ ℤT pr₁
  (EqO,    [     ℤT pr₁, ℤT pr₂ ]) | pr₁ ≡ pr₂ → return 𝔹T
  (LTO,    [     ℤT pr₁, ℤT pr₂ ]) | pr₁ ≡ pr₂ → return 𝔹T
  (LTEO,   [     ℤT pr₁, ℤT pr₂ ]) | pr₁ ≡ pr₂ → return 𝔹T
  (LTEO,   [     ℕT pr₁, ℕT pr₂ ]) | pr₁ ≡ pr₂ → return 𝔹T
  (GTO,    [     ℤT pr₁, ℤT pr₂ ]) | pr₁ ≡ pr₂ → return 𝔹T
  (GTO,    [     ℕT pr₁, ℕT pr₂ ]) | pr₁ ≡ pr₂ → return 𝔹T
  (PlusO,  [     ℕT pr₁, ℕT pr₂ ]) | pr₁ ≡ pr₂ → return $ ℕT pr₁
  (EqO,    [     ℕT pr₁, ℕT pr₂ ]) | pr₁ ≡ pr₂ → return 𝔹T
  (CondO,  [ 𝔹T, 𝔹T,     𝔹T     ])             → return 𝔹T
  (CondO,  [ 𝔹T, ℤT pr₁, ℤT pr₂ ]) | pr₁ ≡ pr₂ → return $ ℤT pr₁
  (CondO,  [ 𝔹T, ℕT pr₁, ℕT pr₂ ]) | pr₁ ≡ pr₂ → return $ ℕT pr₁
  _ → todoError

-- Gets protocol of located type
extractProt :: Type → EM (𝑂 Prot)
extractProt τ =
 case τ of 
  (SecT _  (ShareT p _ _))   → return (Some p)
  (SecT _ _)  → return None
  _ → todoError

assertM :: Mode → Type → EM ()
assertM m τ =
  case τ of 
    (SecT loc _)  →  do
          l ← elabEMode loc
          if (m == l) then return () else todoError 
    _  → todoError

-- Extracts basetype
extractBase :: Type → EM BaseType
extractBase τ =
   case τ of 
     (SecT _ (BaseT bτ))  → return bτ
     (SecT _ (ShareT _ _ (BaseT bτ)))  →  return bτ
     _ → todoError

-----------------
--- Subtype utility ---
-----------------

-- Check if loctyS <: loctyT
subtype_loc :: Type → Type → EM 𝔹
subtype_loc loctyS loctyT = case loctyS of
  -- sigma = bty 
  -- -------Sub-Refl
  -- sigma <: sigma 
  BaseT bty → return (loctyS == loctyT)
  ShareT pS loc loctyS  → case loctyT of
      ShareT pT loc' loctyT → do 
        l ← (elabEMode loc)
        l' ← (elabEMode loc')
        loccond ← (subtype_loc loctyS loctyT)
        return ((l == l') ⩓ (pS == pT) ⩓ loccond)
      _  → return False

  (loctySₗ :+: loctySᵣ) → case loctyT of
    (loctyTₗ :+: loctyTᵣ) → do 

        loccondₗ ← (subtype_loc loctySₗ loctyTₗ)
        loccondᵣ ← (subtype_loc loctySᵣ loctyTᵣ)
        return (loccondₗ ⩓ loccondᵣ)
    _ → return False 
  -- t1 <: t1' t2 <: t2'
  -- -------Sub-Pair
  -- t1 x t2 <: t1' x t2' 
  (loctySₗ :×: loctySᵣ) → case loctyT of
    (loctyTₗ :×: loctyTᵣ) → do 

        loccondₗ ← (subtype_loc loctySₗ loctyTₗ)
        loccondᵣ ← (subtype_loc loctySᵣ loctyTᵣ)
        return (loccondₗ ⩓ loccondᵣ)
    _ → return False
  (ListT _ τₜ)  →  case loctyT of
    (ListT _ τₜ') → (subtype_loc τₜ τₜ')
    _ → return False
  (τ₁₁ :→: (η :* τ₁₂)) → case loctyT of
    (τ₁₁' :→: (η' :* τ₁₂')) → do 
        l ← elabEMode $ effectMode η
        l' ← elabEMode $ effectMode η'
        loccondₗ ← (subtype_loc τ₁₁' τ₁₁)
        loccondᵣ ← (subtype_loc τ₁₂ τ₁₂')
        return ((l == l') ⩓ loccondₗ ⩓ loccondᵣ)
  (RefT None τ) →  return (loctyS == loctyT)
  (RefT _ τ) → case loctyT of
    (RefT None τ') → (subtype_loc τ τ')
    _  → return (loctyS == loctyT)
  (ArrT _ _ τ) →   return (loctyS == loctyT)
  (ArrT _ _ τ) → case loctyT of
    (ArrT None _ τ') → (subtype_loc τ τ')
    _  → return (loctyS == loctyT)

  _ → return False

-- Check if tyS <: tyT
subtype :: Type → Type → EM 𝔹
  -- sigma <: sigma' m ⊇ m'
  -- -------Sub-Loc
  -- sigma@m <: sigma'@m' 
subtype tyS tyT = case tyS of
  SecT locS loctyS → case tyT of
      SecT locT loctyT → do 
        mcond ← (superemode locS locT)
        loccond ← (subtype_loc loctyS loctyT)
        return (mcond ⩓ loccond)
      _ → return False
  _ → return False


-- Check if tyT >: tyS
supertype :: Type → Type → EM 𝔹
supertype tyT tyS = subtype tyS tyT

-- Checks if emT ⊇ emS
superemode :: EMode → EMode → EM 𝔹
superemode locT locS= do
  lT ← elabEMode locT
  lS ← elabEMode locS
  return (supermode lT lS)

-- Checks if mT ⊇ mS
supermode :: Mode → Mode → 𝔹
supermode locT locS = case locT of
  Top → True
  AddTop psT → case locS of
      Top → False
      AddTop psS  → (psT ⊇ psS)

 -- Returns em ∩ em'
inter_em :: EMode → EMode → EM EMode
inter_em loc loc' = do
  l ← elabEMode loc
  l' ← elabEMode loc'
  (elabMode (inter_m l l'))
 
-- Returns m ∩ m'
inter_m :: Mode → Mode → Mode
inter_m l l' = case l of
  Top → l'
  AddTop ps → case l' of
      Top → (AddTop ps)
      AddTop ps'  →  AddTop(ps ∩ ps')

 -- Returns em ∩ em'
union_em :: EMode → EMode → EM EMode
union_em loc loc' = do
  l ← elabEMode loc
  l' ← elabEMode loc'
  (elabMode (union_m l l'))
 
-- Returns m ∩ m'
union_m :: Mode → Mode → Mode
union_m l l' = case l of
  Top → Top
  AddTop ps → case l' of
      Top → Top
      AddTop ps'  →  AddTop(ps ∪ ps')

-----------------
--- Join functions ---
-----------------
-- Finds meet of two located types (subtype of both)
locty_meet :: Type  → Type  → EM Type 
locty_meet locty locty' =
  case locty of
  -- sigma = bty 
  -- -------Sub-Refl
  -- sigma <: sigma 
  BaseT bty → if (locty == locty') then (return locty) else todoError
  ShareT p loc locty  → (case locty' of
    ShareT p' loc' locty' → 
      do 
        l ← (elabEMode loc)
        l' ← (elabEMode loc')
        if ((p == p') ⩓ (l == l'))
          then (
            do
              loc_meet ← (locty_meet locty locty')
              return (ShareT p loc loc_meet)
          )
        else todoError
      
    _  → todoError
    )
  (tyₗ :+: tyᵣ) → case locty' of
    (ty'ₗ :+: ty'ᵣ) → do 

        meet_tyₗ  ← (ty_meet tyₗ ty'ₗ)
        meet_tyᵣ ← (ty_meet tyᵣ ty'ᵣ)
        return (meet_tyₗ :+: meet_tyᵣ)
  -- t1 <: t1' t2 <: t2'
  -- -------Sub-Pair
  -- t1 x t2 <: t1' x t2' 
  (tyₗ :×: tyᵣ) → case locty' of
    (ty'ₗ :×: ty'ᵣ) → do 

        meet_tyₗ  ← (ty_meet tyₗ ty'ₗ)
        meet_tyᵣ ← (ty_meet tyᵣ ty'ᵣ)
        return (meet_tyₗ :×: meet_tyᵣ)

    _ → todoError
  (ListT _ τₜ)  →  case locty' of
    (ListT _ τₜ') → (ty_meet τₜ τₜ')
    _ → todoError
  (τ₁₁ :→: (η :* τ₁₂)) → case locty' of
    (τ₁₁' :→: (η' :* τ₁₂')) → do 
        l ← elabEMode $ effectMode η
        l' ← elabEMode $ effectMode η'
        if (l == l')
          then (
            do
              join_τ₁₁ ← (locty_join τ₁₁ τ₁₁')
              meet_τ₁₂ ← (locty_meet τ₁₂ τ₁₂')
              return (join_τ₁₁ :→: (η :* meet_τ₁₂))
          )
        else todoError
  (RefT None τ)  →  case locty' of
    (RefT (Some _) τ') → do
        loc_meet ← (locty_meet locty locty')
        return (RefT (Some loc) loc_meet)
    _  → if (locty == locty') then (return locty) else todoError
  (RefT (Some loc) τ)  →  case locty' of
      (RefT None τ') → do
        loc_meet ← (locty_meet locty locty')
        return (RefT (Some loc) loc_meet)
      _  → if (locty == locty') then (return locty) else todoError
  (ArrT None _ τ)  →  case locty' of
    (ArrT (Some _) _ τ') do
        loc_meet ← (locty_meet locty locty')
        return (ArrT None _ loc_meet)
    _  → if (locty == locty') then (return locty) else todoError
  (ArrT (Some loc) _ τ)  →  case locty' of
      (ArrT None _ τ') → do
        loc_meet ← (locty_meet locty locty')
        return (ArrT None _ loc_meet)
      _  → if (locty == locty') then (return locty) else todoError
  _ → todoError

-- Finds join of two types
ty_meet :: Type  → Type  → EM Type 
ty_meet ty ty' = case ty of
  SecT loc loc_ty → (case ty' of
      SecT loc' loc_ty' → do 
        loc_union ← (union_em loc loc')
        loc_meet ← (locty_meet loc_ty loc_ty')
        return (SecT loc_union loc_meet)
      ty' → todoError)

  x  → todoError

-- Finds join of two located types
locty_join :: Type  → Type  → EM Type 
locty_join locty locty' =
  case locty of
  -- sigma = bty 
  -- -------Sub-Refl
  -- sigma <: sigma 
  BaseT bty → if (locty == locty') then (return locty) else todoError
  ShareT p loc locty  → (case locty' of
    ShareT p' loc' locty' → 
      do 
        l ← (elabEMode loc)
        l' ← (elabEMode loc')
        if ((p == p') ⩓ (l == l'))
          then (
            do
              loc_join ← (locty_join locty locty')
              return (ShareT p loc loc_join)
          )
        else todoError
      
    _  → todoError
    )
  (tyₗ :+: tyᵣ) → case locty' of
    (ty'ₗ :+: ty'ᵣ) → do 

        join_tyₗ  ← (ty_join tyₗ ty'ₗ)
        join_tyᵣ ← (ty_join tyᵣ ty'ᵣ)
        return (join_tyₗ :+: join_tyᵣ)
  -- t1 <: t1' t2 <: t2'
  -- -------Sub-Pair
  -- t1 x t2 <: t1' x t2' 
  (tyₗ :×: tyᵣ) → case locty' of
    (ty'ₗ :×: ty'ᵣ) → do 

        join_tyₗ  ← (ty_join tyₗ ty'ₗ)
        join_tyᵣ ← (ty_join tyᵣ ty'ᵣ)
        return (join_tyₗ :×: join_tyᵣ)

    _ → todoError
  (ListT _ τₜ)  →  case locty' of
    (ListT _ τₜ') → (ty_join τₜ τₜ')
    _ → todoError
  (τ₁₁ :→: (η :* τ₁₂)) → case locty' of
    (τ₁₁' :→: (η' :* τ₁₂')) → do 
        l ← elabEMode $ effectMode η
        l' ← elabEMode $ effectMode η'
        if (l == l')
          then (
            do
              meet_τ₁₁ ← (locty_meet τ₁₁ τ₁₁')
              join_τ₁₂ ← (locty_join τ₁₂ τ₁₂')
              return (meet_τ₁₁ :→: (η :* join_τ₁₂))
          )
        else todoError
  (ArrT None _ τ)  →  case locty' of
      (ArrT (Some _) _ τ') do
          loc_meet ← (locty_join locty locty')
          return (ArrT (Some loc) _ loc_meet)
      _  → if (locty == locty') then (return locty) else todoError
    (ArrT (Some loc) _ τ)  →  case locty' of
        (ArrT None _ τ') → do
          loc_meet ← (locty_join locty locty')
          return (ArrT (Some loc) _ loc_meet)
        _  → if (locty == locty') then (return locty) else todoError
  _ → todoError

-- Finds join of two types
ty_join :: Type  → Type  → EM Type 
ty_join ty ty' = case ty of
  SecT loc loc_ty → (case ty' of
      SecT loc' loc_ty' → do 
        loc_inter ← (inter_em loc loc')
        loc_top ← (locty_join loc_ty loc_ty')
        return (SecT loc_inter loc_top)
      ty' → todoError)

  x  → todoError

-- Assumes non empty list of well-formed types
joinList :: 𝐿 Type → EM Type
joinList τs =
  case τs of 
    Nil → todoError
    τ :& τs → (mfold τ ty_join τs)

-----------------
--- Well formed fnctions functions ---
-----------------

-- Rules to see if any located value is well-formed
wf_loctype :: Type → Mode → EM ()
wf_loctype sigma m =
  case sigma of
    BaseT bt → return () 
    ShareT p loc locty → do
      _ ← (wf_share_loctype locty m)
      l ← (elabEMode loc)
      -- WF-Enc
      if (m == l) then (return ()) else todoError
    (loctyₗ :+: loctyᵣ) → do 
      _ ← (wf_type loctyₗ m)
      _ ← (wf_type loctyᵣ m)
      return ()
    (loctyₗ :×: loctyᵣ)  → do
      _ ← (wf_type loctyₗ m)
      _ ← (wf_type loctyᵣ m)
      return ()
    (ListT _ τₜ)  → do
      _ ← (wf_type τₜ m)
      return ()
    (τ₁₁ :→: (η :* τ₁₂)) → do
      m  ← askL terModeL
      l ← elabEMode $ effectMode η
      _ ← (wf_type τ₁₁ m)
      _ ← (wf_type τ₁₂ m)
      guardErr (m ≡ l) $
        typeError "Not well formed m != l" $ frhs
        [ ("m", pretty m)
        , ("l", pretty l)
        ]
    (RefT _ τ')  → do
      _ ← (wf_type τ' m)
      return ()
    (ArrT _ _ τ')  →  do
      _ ← (wf_type τ' m)
      return ()
    _  → todoError


-- Rules to see if some located value is well-formed
wf_share_loctype :: Type → Mode → EM ()
wf_share_loctype sigma m =
  case sigma of
    BaseT bt → return () 
    (loctyₗ :+: loctyᵣ) → do 
      _ ← (wf_type loctyₗ m)
      _ ← (wf_type loctyᵣ m)
      return ()
    _  → do
      todoError


-- Rules to see if the type is well formed
wf_type :: Type → Mode → EM ()
wf_type ty m = 
  case ty of 
    SecT em' locty → do
      wfcond ← (wf_loctype locty m)
      m' ← (elabEMode em')
      if (supermode m m') then (return ()) else todoError


-- Rules to get the least sub subtype of loctype sigma that is well formed
sublocty_wf :: Type  → Mode →  EM Type 
sublocty_wf sigma m = 
  case sigma of
    BaseT bt → return sigma
    ShareT p loc loc_ty  → do
        l ← (elabEMode loc)
        if (l == m) then
          do 
            loc_subty ← (share_subloctype_wf loc_ty m)
            return (ShareT p loc loc_subty)
        else
          todoError
    (loctyₗ :+: loctyᵣ) → do 
      loctyₗ' ← (subty_wf loctyₗ m)
      loctyᵣ' ← (subty_wf loctyᵣ m)
      return (loctyₗ' :+: loctyᵣ')
    (loctyₗ :×: loctyᵣ)  → do
      loctyₗ' ← (subty_wf loctyₗ m)
      loctyᵣ' ← (subty_wf loctyᵣ m)
      return (loctyₗ' :×: loctyᵣ')
    (ListT n τₜ)  → do
      τₜ' ← (subty_wf τₜ m)
      return (ListT n τₜ') 
    (τ₁₁ :→: (η :* τ₁₂)) → do
      l ← elabEMode $ effectMode η
      l_inter ← (elabMode (inter_m m l))
      τ₁₁' ← (superty_wf τ₁₁ m)
      τ₁₂' ← (subty_wf τ₁₂ m)
      return (τ₁₁' :→:  (( Effect {effectInput = effectInput η, effectReveal = effectReveal η,  effectMode = l_inter}) :* τ₁₂'))
    (RefT loc τ)  → do
      τ' ← (subty_wf loc τ m)
      return (RefT loc τ')
    (ArrT loc n τ)  → do
      τ' ← (subty_wf τ m)
      return (ArrT loc n τ')
    x  → todoError

-- Rules to get the least super supertype of located type that a share can take sigma that is well formed
share_subloctype_wf :: Type → Mode → EM Type
share_subloctype_wf sigma m =
  case sigma of
    BaseT bt → return sigma
    (loctyₗ :+: loctyᵣ) → do 
      loctyₗ' ← (subty_wf loctyₗ m)
      loctyᵣ' ← (subty_wf loctyᵣ m)
      return (loctyₗ' :+: loctyᵣ')
    _  → todoError

-- Rules to get the least super supertype of type t that is well formed
subty_wf :: Type  → Mode  → EM Type 
subty_wf t m = 
    case t of
    SecT loc loc_ty → do
      loc_subty ← (superlocty_wf loc_ty m)
      wfcond ← (wf_loctype loc_ty m)
      l ← (elabEMode loc)
      if (supermode m l) then (return (SecT loc loc_subty)) else todoError
    _  → todoError


-- Rules to get the least super supertype of loctype sigma that is well formed
superlocty_wf :: Type  → Mode →  EM Type 
superlocty_wf sigma m = 
  case sigma of
    BaseT bt → return sigma
    ShareT p loc loc_ty  → do
        l ← (elabEMode loc)
        if (l == m) then
          do 
            loc_superty ← (share_superloctype_wf loc_ty m)
            return (ShareT p loc loc_superty)
        else
          todoError
    (loctyₗ :+: loctyᵣ) → do 
      loctyₗ' ← (superty_wf loctyₗ m)
      loctyᵣ' ← (superty_wf loctyᵣ m)
      return (loctyₗ' :+: loctyᵣ')
    (loctyₗ :×: loctyᵣ)  → do
      loctyₗ' ← (superty_wf loctyₗ m)
      loctyᵣ' ← (superty_wf loctyᵣ m)
      return (loctyₗ' :×: loctyᵣ')
    (ListT n τₜ)  → do
      τₜ' ← (superty_wf τₜ m)
      return (ListT n τₜ') 
    (τ₁₁ :→: (η :* τ₁₂)) → do
      l ← elabEMode $ effectMode η
      l_inter ← (elabMode (inter_m m l))
      τ₁₁' ← (subty_wf τ₁₁ m)
      τ₁₂' ← (superty_wf τ₁₂ m)
      return (τ₁₁' :→:  (( Effect {effectInput = effectInput η, effectReveal = effectReveal η,  effectMode = l_inter}) :* τ₁₂'))
    (RefT loc τ)  → do
      τ' ← (superty_wf τ m)
      return (RefT loc τ')
    (ArrT loc n τ)  → do
      τ' ← (superty_wf τ m)
      return (ArrT loc n τ')
    x  → todoError

-- Rules to get the least super supertype of located type that a share can take sigma that is well formed
share_superloctype_wf :: Type → Mode → EM Type
share_superloctype_wf sigma m =
  case sigma of
    BaseT bt → return sigma
    (loctyₗ :+: loctyᵣ) → do 
      loctyₗ' ← (superty_wf loctyₗ m)
      loctyᵣ' ← (superty_wf loctyᵣ m)
      return (loctyₗ' :+: loctyᵣ')
    _  → todoError

-- Rules to get the least super supertype of type t that is well formed
superty_wf :: Type  → Mode  → EM Type 
superty_wf t m = 
    case t of
    SecT loc loc_ty → do
        l ← (elabEMode loc)
        l_inter ← (elabMode (inter_m m l))
        loc_superty ← (superlocty_wf loc_ty m)
        return (SecT l_inter loc_superty)
    _  → todoError


-----------------
--- Bind Typing ---
-----------------

bindTo ∷ Var → Type → EM a → EM a
bindTo x τ = mapEnvL terEnvL ((x ↦ τ) ⩌)

bindType ∷ Type → Pat → (EM (EM a → EM a))
bindType τ ψ = matchType τ ψ
-- assume type is well formed
matchType ∷  Type → Pat → EM (EM a → EM a)
matchType τ ψ= case ψ of 
  VarP x → return (bindTo  x τ)
  BulP → case τ of
    (SecT loc (BaseT (UnitT) )) →  do
          m ← askL terModeL
          l ← elabEMode loc
          if (m == l) then return (\x -> x) else todoError
    (SecT loc (ShareT _ _ (BaseT (UnitT) ))) →  do
          m ← askL terModeL
          l ← elabEMode loc
          if (m == l) then return (\x -> x) else todoError 
    _ → todoError
  EPrinSetP  → case τ of
    (SecT loc (BaseT ℙsT)) → do
          m ← askL terModeL
          l ← elabEMode loc
          if (m == l) then return (\x -> x) else todoError
    (SecT loc (ShareT _ _ (BaseT  ℙsT )))   → do 
          m ← askL terModeL
          l ← elabEMode loc
          if (m == l) then return (\x -> x) else todoError
    _ → todoError
  NEPrinSetP x ψ   → case τ of
    (SecT loc (BaseT ℙsT ))  →  do
          m ← askL terModeL
          l ← elabEMode loc
          if (m == l) then
            return (\y -> ( 
            do
            mt ← (bindType  (SecT loc (BaseT ℙsT )) ψ)
            (mt  ((bindTo  x (SecT loc (BaseT ℙT ))) y)) ))
          else
            todoError
    (SecT loc (ShareT p loc' (BaseT  ℙsT )))  → do
          m ← askL terModeL
          l ← elabEMode loc
          if (m == l) then
            return (\y -> ( 
            do
            mt ←  (bindType (SecT loc (ShareT p loc' (BaseT ℙsT ))) ψ)
            (mt ((bindTo  x (SecT loc (ShareT p loc' (BaseT ℙT )))) y) ) ))
          else
            todoError
  ProdP ψₗ ψᵣ  →     case τ of
    (SecT loc (τₗ :×: τᵣ)) → do
        m ← askL terModeL
        l ← elabEMode loc
        if (m == l) then
          return (\x -> ( 
          do
          ml ←  (bindType τₗ ψₗ) 
          mr ←  (bindType τᵣ ψᵣ)
          (mr (ml x)) ))
        else
          todoError
    _ → todoError
  LP ψₗ  → case τ of
    (SecT loc (τₗ  :+: τᵣ)) → do
        m ← askL terModeL
        l ← elabEMode loc
        if (m == l) then
          (bindType τₗ ψₗ)
        else
          todoError
    (SecT loc (ShareT _ _ (τₗ  :+: τᵣ))) → do
        m ← askL terModeL
        l ← elabEMode loc
        if (m == l) then
          (bindType τₗ ψₗ)
        else
          todoError
  RP ψᵣ → case τ of
    (SecT loc (τₗ  :+: τᵣ)) → do
        m ← askL terModeL
        l ← elabEMode loc
        if (m == l) then
           (bindType τᵣ ψᵣ)
        else
          todoError
    (SecT loc (ShareT _ _ (τₗ  :+: τᵣ))) → do
        m ← askL terModeL
        l ← elabEMode loc
        if (m == l) then
           (bindType τᵣ ψᵣ)
        else
          todoError
    _ → todoError
  NilP → case τ of
    (SecT loc (ListT _ τₜ)) → do
          m ← askL terModeL
          l ← elabEMode loc
          if (m == l ) then return (\x -> x) else todoError 
    _ → todoError
  ConsP ψ ψₜ → case τ of
    (SecT loc (ListT n τₜ)) → do
          m ← askL terModeL
          l ← elabEMode loc
          if (m == l) then
            return (\x -> ( 
            do
            mh ←  (bindType τₜ ψ) 
            mt ←  (bindType τ ψₜ)
            (mt (mh x)) ))
          else
            todoError
    _ → todoError
  WildP → return (\x -> x)

------------------------------------------------
-- Static Evaluation of Principal Expressions --
------------------------------------------------
setToList :: (𝑃 a)  → (𝐿 a)
setToList myset = list𝐼 (iter myset)

listToSet :: (Ord a) ⇒ (𝐿 a)  → (𝑃 a)
listToSet mylist = pow𝐼 (iter mylist)

elabPrinExp ∷ PrinExp → EM PrinVal
elabPrinExp ρe = case  ρe of
  VarPE x       → return (SinglePV (𝕩name x))
  AccessPE x n₁ → return (AccessPV (𝕩name x) n₁)

elabPrinSetExp ∷ PrinSetExp → EM (𝑃 PrinVal)
elabPrinSetExp ρse = case  ρse of
  PowPSE ρel → do
    pvl ← (mapM elabPrinExp ρel )
    (let ρvs = (listToSet pvl) in (return ρvs))
 
  x → todoError


elabEMode ∷ EMode → EM Mode
elabEMode = mapM elabPrinSetExp

elabPrinVal :: PrinVal → EM PrinExp
elabPrinVal ρv = case  ρv of
  (SinglePV ρ)    → return (VarPE (var ρ)) 
  (AccessPV ρ n₁) → return (AccessPE (var ρ) n₁)

-- turn powerset to list, map the list, convert to prinsetexp
elabPrinValSet :: (𝑃 PrinVal)  → EM PrinSetExp
elabPrinValSet ρvp = let ρvl = (setToList ρvp) in do
  ρel ← (mapM elabPrinVal ρvl) 
  (return (PowPSE ρel))

elabMode ∷ Mode → EM EMode
elabMode = mapM elabPrinValSet