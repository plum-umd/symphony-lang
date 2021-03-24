module PSL.Interpreter.PrinExp where

import UVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Lens
import PSL.Interpreter.Error
import PSL.Interpreter.Val

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
          throwIErrorCxt TypeIError "interpPrinVar: v ≢ PrinV _" $ frhs
            [ ("v",pretty v)
            , ("γ #? x",pretty (γ ⋕? x))
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
  StarPE _x → throwIErrorCxt NotImplementedIError "principal star" null
    -- do
    -- ρev ← interpPrinVar x
    -- case ρev of
    --   SetPEV n ρ → return $ PowPEV $ pow $ mapOn (upTo n) $ \ i → AccessPV ρ i
    --   _ → throwIErrorCxt TypeIError "ρev.* only works when ρ is the name of a principal set" $ frhs
    --     [ ("ρev",pretty ρev) ]
  ThisPE → do
    m ← askL iCxtGlobalModeL
    case m of
      -- SecM ρv → return $ ValPEV $ ρv
      SecM ρvs → return $ PowPEV $ ρvs
      TopM → throwIErrorCxt NotImplementedIError "Use of 'this' keyword in TopM not implemented" $ frhs
        [ ("m",pretty m)
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

prinExpVals ∷ (STACK) ⇒ PrinExpVal → IM (𝑃 PrinVal)
prinExpVals ρev = case ρev of
  ValPEV v → return $ single v
  PowPEV vs → return $ vs
  SetPEV n ρ → return $
    pow $ mapOn (upTo n) $ \ i → AccessPV ρ i
    -- throwIErrorCxt TypeIError "{A} fails when A is a set of prinples; did you mean {A.*}?" $ frhs
    --   [ ("ρ",pretty ρ) ]

prinExpValss ∷ (STACK,ToIter PrinExpVal t) ⇒ t → IM (𝑃 PrinVal)
prinExpValss = unions ^∘ mapM prinExpVals ∘ list
