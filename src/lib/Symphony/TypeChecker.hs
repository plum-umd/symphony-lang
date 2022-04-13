module Symphony.TypeChecker where

import Symphony.Prelude

import Symphony.Lang.Syntax

import Symphony.TypeChecker.Types

synVar ∷ Var → TM Type
synVar x = do
  γ ← askL tCxtEnvL
  case γ ⋕? x of
    Some τ → return τ
    None   → throwTErrorCxt TypeTError "synVar: x ∉ dom(γ)" $ frhs
             [ ("x", pretty x)
             , ("dom(γ)", pretty $ keys γ)
             ]

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
