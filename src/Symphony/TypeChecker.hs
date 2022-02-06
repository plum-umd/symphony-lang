module Symphony.TypeChecker where

import UVMHS
import AddToUVMHS

import Symphony.Syntax
import Symphony.TypeChecker.Error
import Symphony.TypeChecker.TLM hiding (TLR)
import Symphony.TypeChecker.EM

---------------------
-- Checking for TL --
---------------------

synProg ∷ 𝐿 TL → TLM Type
synProg prog = do
  eachOn prog bindTL
  asTLM $ do
    τMain ← synVar $ var "main"
    synApp τMain $ BaseT UnitT

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

------------------------------
-- Checking for Expressions --
------------------------------

primType ∷ Op → 𝐿 BaseType → m BaseType
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

supertype :: Type → Type → EM 𝔹
supertype tyT tyS = subtype tyS tyT

superemode :: EMode → EMode → EM 𝔹
superemode emT emS= do
  mT ← elabEMode emT
  mS ← elabEMode emS
  return (supermode mT mS)

supermode :: Mode → Mode → 𝔹
supermode mT mS = case mT of
  Top → True
  AddTop sT → case mS of
      Top → False
      AddTop sS  → (sT ⊇ sS)
 
inter_em :: EMode → EMode → EM EMode
inter_em em em' = do
  m ← elabEMode em
  m' ← elabEMode em'
  (elabMode (inter_m m m'))

inter_m :: Mode → Mode → Mode
inter_m m m' = case m of
  Top → m'
  AddTop m → case m' of
      Top → (AddTop m)
      AddTop m'  →  AddTop(m ∩ m')

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

join_wf :: Type → Type → Mode → EM Type 
join_wf ty ty' m =
  do 
  join_ty ← (ty_join ty ty')
  case join_ty of
    SecT em loc_ty → do
        em'' ← (elabMode m)
        em_inter ← (inter_em em em'')
        return (SecT em_inter loc_ty)
    ShareT p em locty  → do
        em'' ← (elabMode m)
        em_inter ← (inter_em em em'')
        return (ShareT p em_inter locty)
    x  → todoError

superlocty_wf :: Type  → EM Type 
superlocty_wf sigma m = 
  case sigma of
    BaseT bt → return bt 
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

share_superloctype_wf :: Type → Mode → EM ()
share_superloctype_wf sigma m =
  case sigma of
    BaseT bt → return bt 
    (loctyₗ :+: loctyᵣ) → do 
      loctyₗ' ← (superty_wf loctyₗ m)
      loctyᵣ' ← (superty_wf loctyᵣ m)
      return (loctyₗ' :+: loctyᵣ')
    x  → todoError

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

-- make_wf :: 
synVar ∷ Var → EM Type
synVar x = do
  env ← askL terEnvL
  case env ⋕? x of
    Some τ → (superty_wf τ)
    None   → typeError "synVar: x ∉ Γ" $ frhs
             [ ("x", pretty x)
             , ("Γ", pretty $ keys env)
             ]

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
  x    →  todoError



synPrim ∷ Op → 𝐿 Exp → EM Type
synPrim op es =
  if (isEmpty es) then
    primType op es
  else
    do 
      m ← askL terModeL
      em ← elabMode m
      τs ← (mapM synExp es)
      _ ← (mapM assertM m τs)
      ps ← (mapM extractProt τs)
      case ps of
        (pOption :& _) →
          if (andf ps (\p -> (pOption == p))) then
            (let bt = (primType op τs) in
            case pOption of
              None →(SecT em bt)
              Some p →(ShareT p em bt)
            )
   
          else
            todoError

extractProt :: Type → EM (𝑂 Prot)
extractProt τ =
 case τ of 
  (SecT _ _)  → None
  (ShareT p _ _)  →  Some p
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

extractBase :: Type → EM BaseType
extractBase τ =
   case τ of 
     (SecT _ (BaseT bτ))  → return bτ
     (ShareT _ _ (BaseT bτ))  →  return bτ
     _ → todoError
     
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
        m  ← askL terModeL
        wfcond ← (wf_type τ m)
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
        wfcond ← (wf_type τ m)
        if subcond then
          return ()
        else
          todoError
    x → todoError

{- Todo: Check if m is a subset of the real mode-}
checkNil ∷ Type → EM ()
checkNil τ =  
  do
    m  ← askL terModeL
    wfcond ← (wf_type τ m)
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
        join_t ← (join_wf τ  τₜ m)
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
      (join_wf τ₂ τ₃ m)
    else
      todoError
{--}
--synCase ∷ Exp → 𝐿 (Pat ∧ Exp) → EM Type
--synCase e ψes =
{-
synCond :: Exp → Exp → Exp → EM Type
synCond e₁ e₂ e₃ =
  let c₁ = synExp e₁
      c₂ = synExp e₂
      c₃ = synExp e₃
  in do
    τ₁  ← c₁
    case τ₁ of
       (SecT em' (τₗ  :+: τᵣ)) → do
        τ₂ ← c₂
        τ₃ ← c₃
        m ← askL terModeL
        m' ← elabEMode em'
        if (supermode m' m) then do
          (join_wf τ₂ τ₃ m)
        else
          todoError
-}
chkLam ∷ 𝑂 Var → 𝐿 Pat → Exp → Type → EM ()
chkLam self𝑂 ψs e τ = todoError

synApp ∷ Type → Type → EM Type
synApp τ₁ τ₂ = case τ₁ of
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

synAscr :: Exp → Type →  EM Type
synAscr e τ = do 
  _ ← (chkExp e τ)
  return τ


chkExp :: Exp → Type → EM ()
chkExp e τ = chkExpR (extract e) τ

chkExpR :: ExpR → Type → EM ()  
chkExpR e τ = case e of
  LE eₗ        → checkL eₗ τ
  RE eᵣ        → checkR eᵣ τ
  NilE        → checkNil τ
  _ →     
        do 
        m  ← askL terModeL
        wfcond ← (wf_type τ m)
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
  PrinSetE es → synPrinSet es
  PrinE e → checkPrin e

  ProdE eₗ eᵣ  → synProd eₗ eᵣ
  ConsE eₕ eₜ  → synCons eₕ eₜ
  IfE e₁ e₂ e₃ → synIf e₁ e₂ e₃
--CaseE e ψes  → synCase e ψes

  AscrE e τ → synAscr e τ

  -- PrimE op es → synPrim op es
  _      → undefined
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
