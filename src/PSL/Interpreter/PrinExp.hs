module PSL.Interpreter.PrinExp where

import UVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Access

interpPrinVar ∷ (STACK) ⇒ 𝕏 → IM PrinExpVal
interpPrinVar x = do
  γ ← askL iCxtEnvL
  case γ ⋕? x of
    Some ṽ → do
      v ← elimValP ṽ
      case v of
        PrinV ρev → return ρev
        PrinSetV ρvs → return $ PowPEV ρvs
        _ → do
          traceM "HERE" 
          throwIErrorCxt TypeIError "interpPrinVar: v ≢ PrinV _" $ frhs
            [ ("v",pretty v)
            ]
    _ → throwIErrorCxt TypeIError "interpPrinVar: x ∉ dom(γ)" $ frhs
      [ ("x",pretty x)
      , ("dom(γ)",pretty $ keys γ)
      ]

interpPrinExp ∷ (STACK) ⇒ PrinExp → IM PrinExpVal
interpPrinExp ρe = case ρe of
  VarPE x → interpPrinVar x
  AccessPE x i → do
    ρev ← interpPrinVar x
    case ρev of
      SetPEV n ρx | i < n → return $ ValPEV $ AccessPV ρx i
      _ → throwIErrorCxt TypeIError "interpPrinExp: ρev ≢ SetPEV _ _" $ frhs
        [ ("ρev",pretty ρev)
        ]

interpPrinExpSingle ∷ (STACK) ⇒ PrinExp → IM PrinVal
interpPrinExpSingle ρe = do
  ρv ← interpPrinExp ρe
  case ρv of
    ValPEV v → return v
    PowPEV vs | [v] ← tohs $ list vs → return v
    _ → throwIErrorCxt TypeIError "interpPrinExpSingle: ρv ∉ {SinglePEV _,AccessPEV _ _}" $ frhs
      [ ("ρv",pretty ρv)
      ]

prinExpVals ∷ (STACK) ⇒ PrinExpVal → 𝑃 PrinVal
prinExpVals ρev = case ρev of
  ValPEV v → single v
  SetPEV n ρ → pow $ mapOn (upTo n) $ \ i → AccessPV ρ i
  PowPEV vs → vs

prinExpValss ∷ (STACK,ToIter PrinExpVal t) ⇒ t → 𝑃 PrinVal
prinExpValss = unions ∘ map prinExpVals ∘ iter
