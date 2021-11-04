module Symphony.TypeChecker where

import UVMHS
import AddToUVMHS

import Symphony.Syntax
import Symphony.TypeChecker.Types


------------------
--- Primitives ---
------------------

synVar ∷ Var → TM Type
synVar x = do
  γ ← askL tCxtEnvL
  case γ ⋕? x of
    Some τ → return τ
    None   → throwTErrorCxt TypeTError "synVar: x ∉ dom(γ)" $ frhs
             [ ("x", pretty x)
             , ("dom(γ)", pretty $ keys γ)
             ]

synBul ∷ TM Type
synBul = return $ BaseT UnitT

synBool ∷ 𝔹 → TM Type
synBool _ = return $ BaseT 𝔹T

synNat ∷ IPrecision → ℕ → TM Type
synNat pr _ = return $ BaseT (ℕT pr)

synInt ∷ IPrecision → ℤ → TM Type
synInt pr _ = return $ BaseT (ℤT pr)

synFlt ∷ FPrecision → 𝔻 → TM Type
synFlt pr _ = return $ BaseT (𝔽T pr)

synStr ∷ 𝕊 → TM Type
synStr _ = return $ BaseT 𝕊T

synExp ∷ ExpR → TM Type
synExp e = case e of
   -- Variables
  VarE x → synVar x

  -- Literals
  BulE        → synBul
  BoolE b     → synBool b
  NatE pr n   → synNat pr n
  IntE pr z   → synInt pr z
  FltE pr d   → synFlt pr d
  StrE s      → synStr s

  _      → undefined

synDecl ∷ Var → Type → TM a → TM a
synDecl x τ = mapEnvL tCxtEnvL ((x ↦ τ) ⩌)

synDefn ∷ Var → 𝐿 Pat → Exp → TM a → TM a
synDefn x ψs e = undefined

synPrin ∷ 𝐿 PrinDecl → TM a → TM a
synPrin ρds = undefined

synTypeTL ∷ TL → TM a → TM a
synTypeTL tl = case extract tl of
  DeclTL _b x τ    → synDecl x τ
  DefnTL _b x ψs e → synDefn x ψs e
  PrinTL ρds       → synPrin ρds
  ImportTL path    → \ _ → throwTErrorCxt NotImplementedTError "import" Nil

synTypeTLs ∷ 𝐿 TL → TM Type
synTypeTLs tls = case tls of
  Nil → synVar $ var "main" -- TODO(ian): check that it actually has type (unit@T ->T <something>) where <something> is first-order
  tl :& tls' → let f = synTypeTL tl in f $ synTypeTLs tls'

wellTyped ∷ 𝐿 TL → TM ()
wellTyped tls = do
  _ ← synTypeTLs tls
  return ()
