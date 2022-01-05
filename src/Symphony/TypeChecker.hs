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
synBul =  do
  mode ← askL terMode
  return $ SecT $ (BaseT $ UnitT) mode

interpBool ∷ (STACK, Value v) ⇒ 𝔹 → IM v v
interpBool b = introVal $ BaseV $ Clear $ BoolV b

interpNat ∷ (STACK, Value v) ⇒ IPrecision → ℕ → IM v v
interpNat pr n = introVal $ BaseV $ Clear $ NatV pr n

interpInt ∷ (STACK, Value v) ⇒ IPrecision → ℤ → IM v v
interpInt pr z = introVal $ BaseV $ Clear $ IntV pr z

interpFlt ∷ (STACK, Value v) ⇒ FPrecision → 𝔻 → IM v v
interpFlt pr d = introVal $ BaseV $ Clear $ FltV pr d

interpStr ∷ (STACK, Value v) ⇒ 𝕊 → IM v v
interpStr s = introVal $ BaseV $ Clear $ StrV s

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

synExp ∷ ExpR → TM Type
synExp e = case e of
   -- Variables
  VarE x → synVar x

  -- Literals--
  BulE        → synBul
  _      → undefined
------------------------------------------------
-- Static Evaluation of Principal Expressions --
------------------------------------------------

elabPrinExp ∷ PrinExp → EM PrinVal
elabPrinExp ρe = todoError

elabPrinSetExp ∷ PrinSetExp → EM (𝑃 PrinVal)
elabPrinSetExp ρse = todoError

elabEMode ∷ EMode → EM Mode
elabEMode = mapM elabPrinSetExp

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
