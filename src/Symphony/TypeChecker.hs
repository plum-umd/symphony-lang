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
synBul = return (SecT (AddTop ThisPSE) (BaseT UnitT))

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

checkPrin ∷ PrinExp → Type
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

synExp ∷ ExpR → EM Type
synExp e = case e of
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
  -- PrimE op es → synPrim op es
  _      → undefined
------------------------------------------------
-- Static Evaluation of Principal Expressions --
------------------------------------------------

elabPrinExp ∷ PrinExp → EM PrinVal
elabPrinExp ρe = case  ρe of
  VarPE x       → return (SinglePV (𝕩name x))
  AccessPE x n₁ → return (AccessPV (𝕩name x) n₁)

elabPrinSetExp ∷ PrinSetExp → EM (𝑃 PrinVal)
elabPrinSetExp ρse = todoError

elabEMode ∷ EMode → EM Mode
elabEMode = mapM elabPrinSetExp

--elabMode ∷ Mode → EMode
--elabMode = mapM elabPrinSetExp


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
