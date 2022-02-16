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
  (SecT _ _)  → return None
  (SecT _  (ShareT p _ _))   → return (Some p)
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
     (SecT _ _ (ShareT _ _ (BaseT bτ)))  →  return bτ
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
      AddTop sS  → (psT ⊇ psS)

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
  AddTop m → case l' of
      Top → (AddTop l)
      AddTop m'  →  AddTop(l ∩ l')



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
  ShareT p loc locty  → (case ty' of
    ShareT p' locl' locty' → 
      do 
        l ← (elabEMode loc)
        l' ← (elabEMode loc')
        if ((p == p') ⩓ (l == l'))
          then (
            do
              loc_top ← (locty_join locty locty')
              return (ShareT p loc loc_top)
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
    ShareT p loc loc_ty  → do
        l ← (elabEMode loc)
        if (l == m) then
          do 
            loc_superty ← (share_superloctype_wf loc_ty m)
            return (ShareT p em_inter loc_superty)
        else
          return ()
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
        l ← (elabMode loc)
        m_inter ← (inter_m m l)
        l_inter ← (elabMode m_inter)
        loc_superty ← (superlocty_wf loc_ty m)
        return (SecT l_inter loc_superty)
    _  → todoError


-----------------
--- Bind Typing ---
-----------------

bindTo ∷ Var → Type → EM Type → EM Type
bindTo x τ = mapEnvL terEnvL ((x ↦ τ) ⩌)

bindType ∷ Type → Pat → (EM (EM Type → EM Type))
bindType τ ψ = matchType τ ψ
-- assume type is well formed
matchType ∷  Type → Pat → EM (EM Type → EM Type)
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
          if (m == m') then
            return (\y -> ( 
            do
            mt ←  (bindType (SecT loc (ShareT p loc' (BaseT ℙsT ))) ψ)
            (mt ((bindTo  x (SecT loc (ShareT p loc' (BaseT ℙT )))) y) ) ))
          else
            todoError
  ProdP ψₗ ψᵣ  →     case τ of
    (SecT loc (τₗ :×: τᵣ)) → do
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
    (SecT em' (τₗ  :+: τᵣ)) → do
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