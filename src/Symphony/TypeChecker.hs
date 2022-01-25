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

subtype_loc :: Type → Type → EM 𝔹
subtype_loc loctyS loctyT = case loctyS of
  -- sigma = bty 
  -- -------Sub-Refl
  -- sigma <: sigma 
  BaseT bty → return (loctyS == loctyT)

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

locty_top :: Type  → Type  → EM Type 
locty_top locty locty' =
  case locty of
  -- sigma = bty 
  -- -------Sub-Refl
  -- sigma <: sigma 
  BaseT bty → if (locty == locty') then (return locty) else todoError

  -- t1 <: t1' t2 <: t2'
  -- -------Sub-Pair
  -- t1 x t2 <: t1' x t2' 
  (tyₗ :×: tyᵣ) → case locty' of
    (ty'ₗ :×: ty'ᵣ) → do 

        top_tyₗ  ← (ty_top tyₗ ty'ₗ)
        top_tyᵣ ← (ty_top tyᵣ ty'ᵣ)
        return (top_tyₗ :×: top_tyᵣ)
    x → todoError

  x → todoError

ty_top :: Type  → Type  → EM Type 
ty_top ty ty' = case ty of
  SecT em loc_ty → (case ty' of
      SecT em' loc_ty' → do 
        em_inter ← (inter_em em em')
        loc_top ← (locty_top loc_ty loc_ty')
        return (SecT em_inter loc_top)
      ty' → todoError)
  ShareT p em locty  → (case ty' of
      ShareT p' em' locty' → 
        (if (p == p') 
          then (
          do
            em_inter ← (inter_em em em')
            loc_top ← (locty_top locty locty')
            return (ShareT p em_inter loc_top)
            )
            else todoError
        )
      x  → todoError
      )
  x  → todoError

top_wf :: Type → Type → Mode → EM Type 
top_wf ty ty' m =
  do 
  top_ty ← (ty_top ty ty')
  case top_ty of
    SecT em loc_ty → do
        em'' ← (elabMode m)
        em_inter ← (inter_em em em'')
        return (SecT em_inter loc_ty)
    ShareT p em locty  → do
        em'' ← (elabMode m)
        em_inter ← (inter_em em em'')
        return (ShareT p em_inter locty)
    x  → todoError
-- make_wf :: 
synVar ∷ Var → EM Type
synVar x = do
  env ← askL terEnvL
  case env ⋕? x of
    Some τ → return τ
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
    return (SecT Top (BaseT ℙsT))
  x    →  todoError


--synOp :: Op -> OpType
--synOp op = (BaseOpT (Nat))
-- Gets the operation, gets if the operation needs a specific type or any basic type, gets the type of first type
-- checks if it is the basic ,type, goes through each thing in the list to get the supertype of every type 
-- and that there is a supertype of every type in the list. Can do this by making accumulator first type of the list
-- and true and checking that there exists a supertype for each in the fold
--synPrim ∷ Op → 𝐿 Exp → IM v v
--synPrim op es =
  
  -- arrity
 --   if (getSize op) == (size es) then
 --( 
   -- true if empty
     {-
   if (isEmpty es) then
     return (synRes op)
  else 
    
    case (synOp op) of
    -- Check first element is basetype and then make sure all elements are of a certain supertype
    | AllOp → (let h = (fst es) in 
      do 
      accτ ←  (synExp es)
      if  (isBase accτ) then 
        (case (fold (snd es) (accτ, True) getSuperType2) of
           (_, False) → todoError
           _ → return (synRes op)
        ) 
        else 
        todoError

    -- Check that all elements are a subtype of the type it must be (or the type is a supertype of all)
    |  accτ → 
    (if (fold es True (supertype acct) ) then
      return (synRes op)
           else  todoError
          
      )
 )
  else
    todoError


getSuperType :: ExpR →  (Type, bool) →  (Type, bool)
getSuperType e acc  =
  case acc of
    (_, False) → (accτ, False)
    (accτ, _) →
    let c = synExp e
   in do
    τ ← c
    if subtype accτ τ then (τ, True)
    else (if subtype τ accτ then (accτ, True) else  (accτ, False))
    -}
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

{-}
synLAnno ∷ Exp → Type → EM Type
synLAnno eₗ  =
  case τ of
  |   τₗ  :+: τᵣ →
  let cₗ = synExp eₗ
  in do

    cτₗ  ← cₗ
  if (subtype cₗ τₗ) then
    return τ 
  else
    todoError
  | _ → todoError

synRAnn ∷ Exp → Type → EM Type
synRAnno eₗ  =
  case τ of
  | τₗ  :+: τᵣ
  let cᵣ = synExp eᵣ
  in do
    cτᵣ  ← cᵣ
  if (subtype cᵣ τᵣ) then
    return τ 
  else
    todoError
  | _ → todoError
-}

{- Todo: Check if m is a subset of the real mode-}
synNilAnn ∷ Type → EM Type
synNilAnn τ =  case τ of
  SecT m (ListT _ τₜ)  → return τ
  ShareT φ m (ListT _ τₜ)   → return τ
  x  → todoError
{-}
synCons ∷ Exp → Exp → EM Type
synCons eₕ eₜ =
  let cₕ = synExp eₕ
      cₜ = synExp eₜ
  in do
    τ  ← cₕ
    τs ← cₜ
    case τs of
      {- Check if m is a subset of actual m'? -}
      SecT m' (ListT _ τₜ)  →(if subtype τₜ τ then return  (ListT n τ) else (if subtype τ τₜ then (return τs) else todoError))
      ShareT φ m' (ListT _ τₜ)   → (if subtype τₜ τ then return  (ListT n τ) else (if subtype τ τₜ then (return τs) else todoError))
      _ → todoError
-}

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
    em  ← elabEMode m
    subcond ← (subtype (SecT em (BaseT 𝔹T)) τ₁)
    if subcond then do
      (top_wf τ₂ τ₃ m)
    else todoError

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
synAscr e τ = synExpR $ extract e

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

  IfE e₁ e₂ e₃ → synIf e₁ e₂ e₃
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
