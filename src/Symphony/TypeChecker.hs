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

subtype :: Type → Type → 𝔹
subtype tyS tyT = tyS == tyT

supertype :: Type → Type → 𝔹
supertype tyT tyS = subtype tyS tyT

synVar ∷ Var → EM Type
synVar x = do
  env ← askL terEnvL
  case env ⋕? x of
    Some τ → return τ
    None   → typeError "synVar: x ∉ Γ" $ frhs
             [ ("x", pretty x)
             , ("Γ", pretty $ keys env)
             ]


synBul ∷ EM Type
synBul = 
  do
  m ← askL terModeL
  em ← elabMode m
  return (SecT em (BaseT UnitT))

synBool ∷ 𝔹 → EM Type
synBool b = return (SecT (AddTop ThisPSE) (BaseT 𝔹T))

synNat ∷ IPrecision → ℕ → EM Type
synNat pr n = return (SecT (AddTop ThisPSE) (BaseT (ℕT pr)))

synInt ∷ IPrecision → ℤ → EM Type
synInt pr z = return (SecT (AddTop ThisPSE) (BaseT (ℤT pr)))

synFlt ∷ FPrecision → 𝔻 → EM Type
synFlt pr d = return (SecT (AddTop ThisPSE) (BaseT (𝔽T pr)))

synStr ∷  𝕊 → EM Type
synStr s = return (SecT (AddTop ThisPSE) (BaseT 𝕊T))


synPrinExp ∷ PrinExp → EM Type
synPrinExp ρe = case ρe of
  VarPE x       → synVar x
  AccessPE x n₁ → synVar x

checkPrin ∷ PrinExp → EM Type
checkPrin ρe =
   do
    ρτ ← (synPrinExp ρe) 
    case (subtype ρτ (SecT Top (BaseT ℙT))) of
      True → return (SecT Top (BaseT ℙT))
      False → todoError
    

synPrinSet ∷ PrinSetExp → EM Type
synPrinSet ρse =
  case ρse of
  VarPSE x   → do
    ρsτ ← synVar x
    case (subtype ρsτ (SecT Top (BaseT ℙsT))) of
      True → return (SecT Top (BaseT ℙsT))
      False → todoError
  PowPSE ρes → do
    _ ←  mapM checkPrin ρes
    return (SecT Top (BaseT ℙsT))
  ThisPSE    →  return (SecT Top (BaseT ℙsT))


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
---------------------------------
--- Products, Sums, and Lists ---
---------------------------------

-- Gets the type of the first, gets type of the second, returns the pair located value
synProd ∷  Exp → Exp → EM Type
synProd eₗ eᵣ =
  let cₗ = synExp eₗ
      cᵣ = synExp eᵣ
  in do
    τₗ ← cₗ
    τᵣ ← cᵣ
    return (τₗ :×: τᵣ)

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
{-
interpIf ∷ (STACK, Value v) ⇒ Exp → Exp → Exp → IM v v
interpIf e₁ e₂ e₃ =
  let c₁ = interpExp e₁
      c₂ = interpExp e₂
      c₃ = interpExp e₃
  in do
    b ← elimBool *$ elimClear *$ elimBase *$ elimVal *⋅ c₁
    if b then c₂ else c₃
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

  AscrE e τ → synAscr e τ
  -- PrimE op es → synPrim op es
  _      → undefined
------------------------------------------------
-- Static Evaluation of Principal Expressions --
------------------------------------------------
setToList :: (𝑃 a)  → (𝐿 a)
setToList myset = list𝐼 (UVMHS.Core.Data.Stream.iter𝑃 myset)

listToSet :: (𝐿 a)  → (𝑃 a)
listToSet mylist = pow𝐼 (iter𝐼 mylist)

elabPrinExp ∷ PrinExp → EM PrinVal
elabPrinExp ρe = case  ρe of
  VarPE 𝕏       → return (SinglePV (𝕩name 𝕏))
  AccessPE 𝕏 n₁ → return (AccessPV (𝕩name 𝕏) n₁)

elabPrinSetExp ∷ PrinSetExp → EM (𝑃 PrinVal)
elabPrinSetExp ρse = case  ρse of
  PowPSE ρel → let pvl = (mapM ρel elabPrinExp) in let ρvs = (listToSet ρvl) in PowPSV ρvs
 
  _ → todoError


elabEMode ∷ EMode → EM Mode
elabEMode = mapM elabPrinSetExp

elabPrinVal :: PrinVal → EM PrinExp
elabPrinVal ρv = case  ρv of
  (SinglePV ρ)    → return (VarPE (var ρ)) 
  (AccessPV ρ n₁) → return (AccessPE (var ρ) n₁)

-- turn powerset to list, map the list, convert to prinsetexp
elabPrinValSet :: (𝑃 PrinVal)  → EM PrinSetExp
elabPrinValSet ρvp = let ρvl = (setToList ρvp) in
  let ρel = (mapM ρvl elabPrinVal) in (return PowPSE ρel)

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
