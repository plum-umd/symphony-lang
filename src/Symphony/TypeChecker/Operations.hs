module Symphony.TypeChecker.Operations where

import UVMHS
import AddToUVMHS

import Symphony.Syntax


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
  (SecT _ _)  → return None
  (ShareT p _ _)  → return (Some p)
  _ → todoError

assertM :: Mode → Type → EM ()
assertM m τ =
  case τ of 
    (SecT em' _)  →  do
          m' ← elabEMode em'
          if (m == m') then return () else todoError 
    (ShareT _ em' _)  → do
          m' ← elabEMode em'
          if (m == m') then return () else todoError
    _  → todoError

-- Extracts basetype
extractBase :: Type → EM BaseType
extractBase τ =
   case τ of 
     (SecT _ (BaseT bτ))  → return bτ
     (ShareT _ _ (BaseT bτ))  →  return bτ
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
    
  x → return False

-- Check if tyS <: tyT
subtype :: Type → Type → EM 𝔹
  -- sigma <: sigma' m ⊇ m'
  -- -------Sub-Loc
  -- sigma@m <: sigma'@m' 
subtype tyS tyT = case tyS of
  SecT emS loctyS → case tyT of
      SecT emT loctyT → do 
        mcond ← (superemode emS emT)
        loccond ← (subtype_loc loctyS loctyT)
        return (mcond ⩓ loccond)
      tyT → return False
  ShareT pS emS loctyS  → case tyT of
      ShareT pT emT loctyT → do 
        mcond ← (superemode emS emT)
        loccond ← (subtype_loc loctyS loctyT)
        return (mcond ⩓ (pS == pT) ⩓ loccond)
      tyT  → return False
  x → return False


-- Check if tyT >: tyS
supertype :: Type → Type → EM 𝔹
supertype tyT tyS = subtype tyS tyT



-- Checks if emT ⊇ emS
superemode :: EMode → EMode → EM 𝔹
superemode emT emS= do
  mT ← elabEMode emT
  mS ← elabEMode emS
  return (supermode mT mS)

-- Checks if mT ⊇ mS
supermode :: Mode → Mode → 𝔹
supermode mT mS = case mT of
  Top → True
  AddTop sT → case mS of
      Top → False
      AddTop sS  → (sT ⊇ sS)

 -- Returns em ∩ em'
inter_em :: EMode → EMode → EM EMode
inter_em em em' = do
  m ← elabEMode em
  m' ← elabEMode em'
  (elabMode (inter_m m m'))
 
-- Returns m ∩ m'
inter_m :: Mode → Mode → Mode
inter_m m m' = case m of
  Top → m'
  AddTop m → case m' of
      Top → (AddTop m)
      AddTop m'  →  AddTop(m ∩ m')



-----------------
--- Join functions ---
-----------------

-- Finds join of two located types
locty_join :: Type  → Type  → EM Type 
locty_join locty locty' =
  case locty of
  -- sigma = bty 
  -- -------Sub-Refl
  -- sigma <: sigma 
  BaseT bty → if (locty == locty') then (return locty) else todoError
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

    x → todoError

  x → todoError

-- Finds join of two types
ty_join :: Type  → Type  → EM Type 
ty_join ty ty' = case ty of
  SecT em loc_ty → (case ty' of
      SecT em' loc_ty' → do 
        em_inter ← (inter_em em em')
        loc_top ← (locty_join loc_ty loc_ty')
        return (SecT em_inter loc_top)
      ty' → todoError)
  ShareT p em locty  → (case ty' of
      ShareT p' em' locty' → 
        (if (p == p') 
          then (
          do
            em_inter ← (inter_em em em')
            loc_top ← (locty_join locty locty')
            return (ShareT p em_inter loc_top)
            )
            else todoError
        )
      x  → todoError
      )
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
    x  → todoError


-- Rules to see if some located value is well-formed
wf_share_loctype :: Type → Mode → EM ()
wf_share_loctype sigma m =
  case sigma of
    BaseT bt → return () 
    (loctyₗ :+: loctyᵣ) → do 
      _ ← (wf_type loctyₗ m)
      _ ← (wf_type loctyᵣ m)
      return ()
    x  → do
      todoError


-- Rules to see if the type is well formed
wf_type :: Type → Mode → EM ()
wf_type ty m = 
  case ty of 
    SecT em' locty → do
      wfcond ← (wf_loctype locty m)
      m' ← (elabEMode em')
      if (supermode m m') then (return ()) else todoError
    ShareT p em' locty → do
      wfcond ← (wf_share_loctype locty m)
      m' ← (elabEMode em')
      if (supermode m m') then (return ()) else todoError

-- Rules to get the least super supertype of loctype sigma that is well formed
superlocty_wf :: Type  → Mode →  EM Type 
superlocty_wf sigma m = 
  case sigma of
    BaseT bt → return sigma
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
    x  → todoError

-- Rules to get the least super supertype of type t that is well formed
superty_wf :: Type  → Mode  → EM Type 
superty_wf t m = 
    case t of
    SecT em loc_ty → do
        em'' ← (elabMode m)
        em_inter ← (inter_em em em'')
        loc_superty ← (superlocty_wf loc_ty m)
        return (SecT em_inter loc_superty)
    ShareT p em loc_ty  → do
        em'' ← (elabMode m)
        em_inter ← (inter_em em em'')
        loc_superty ← (share_superloctype_wf loc_ty m)
        return (ShareT p em_inter loc_superty)
    x  → todoError


-----------------
--- Bind Typing ---
-----------------

bindTo ∷ Var → Type → EM Type → EM Type
bindTo x τ = mapEnvL terEnvL ((x ↦ τ) ⩌)

bindType ∷ Type → Pat → (EM (EM Type → EM Type))
bindType τ ψ = matchType τ ψ
 
matchType ∷  Type → Pat → EM (EM Type → EM Type)
matchType τ ψ= case ψ of 
  VarP x → return (bindTo  x τ)
  BulP → case τ of
    (SecT em' (BaseT (UnitT) )) →  do
          m ← askL terModeL
          m' ← elabEMode em'
          if (m == m') then return (\x -> x) else todoError
    (ShareT _ em' (BaseT (UnitT) )) →  do
          m ← askL terModeL
          m' ← elabEMode em'
          if (m == m') then return (\x -> x) else todoError 
    _ → todoError
  EPrinSetP  → case τ of
    (SecT em' (BaseT ℙsT)) → do
          m ← askL terModeL
          m' ← elabEMode em'
          if (m == m') then return (\x -> x) else todoError
    (ShareT p em' (BaseT ℙsT ))  → do 
          m ← askL terModeL
          m' ← elabEMode em'
          if (m == m') then return (\x -> x) else todoError
    _ → todoError
  NEPrinSetP x ψ   → case τ of
    (SecT em' (BaseT ℙsT ))  →  do
          m ← askL terModeL
          m' ← elabEMode em'
          if (m == m') then
            return (\y -> ( 
            do
            mt ← (bindType  (SecT em' (BaseT ℙsT )) ψ)
            (mt  ((bindTo  x (SecT em' (BaseT ℙT ))) y)) ))
          else
            todoError
    (ShareT p em' (BaseT ℙsT ))  → do
          m ← askL terModeL
          m' ← elabEMode em'
          if (m == m') then
            return (\y -> ( 
            do
            mt ←  (bindType (ShareT p em' (BaseT ℙsT )) ψ)
            (mt ((bindTo  x (ShareT p em' (BaseT ℙT ))) y) ) ))
          else
            todoError
  ProdP ψₗ ψᵣ  →     case τ of
    (SecT em' (τₗ :×: τᵣ)) → do
        m ← askL terModeL
        m' ← elabEMode em'
        if (m == m') then
          return (\x -> ( 
          do
          ml ←  (bindType τₗ ψₗ) 
          mr ←  (bindType τᵣ ψᵣ)
          (mr (ml x)) ))
        else
          todoError
    _ → todoError
  LP ψₗ  → case τ of
    (SecT em' (τₗ  :+: τᵣ)) → do
        m ← askL terModeL
        m' ← elabEMode em'
        if (m == m') then
          (bindType τₗ ψₗ)
        else
          todoError
    (ShareT _ em' (τₗ  :+: τᵣ)) → do
        m ← askL terModeL
        m' ← elabEMode em'
        if (m == m') then
          (bindType τₗ ψₗ)
        else
          todoError
  RP ψᵣ → case τ of
    (SecT em' (τₗ  :+: τᵣ)) → do
        m ← askL terModeL
        m' ← elabEMode em'
        if (m == m') then
           (bindType τᵣ ψᵣ)
        else
          todoError
    (ShareT _ em' (τₗ  :+: τᵣ)) → do
        m ← askL terModeL
        m' ← elabEMode em'
        if (m == m') then
           (bindType τᵣ ψᵣ)
        else
          todoError
    _ → todoError
  NilP → case τ of
    (SecT em' (ListT _ τₜ)) → do
          m ← askL terModeL
          m' ← elabEMode em'
          if (m == m') then return (\x -> x) else todoError 
    _ → todoError
  ConsP ψ ψₜ → case τ of
    (SecT em' (ListT n τₜ)) → do
          m ← askL terModeL
          m' ← elabEMode em'
          if (m == m') then
            return (\x -> ( 
            do
            mh ←  (bindType τₜ ψ) 
            mt ←  (bindType τ ψₜ)
            (mt (mh x)) ))
          else
            todoError
    _ → todoError
  WildP → return (\x -> x)

