module PSL.Interpreter.Plain where

import UVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Error
import PSL.Interpreter.Lens
import PSL.Interpreter.Primitives
import PSL.Interpreter.Pretty ()

instance Protocol 'PlainP where
  type ProtocolVal 'PlainP = BaseVal

  typeOf ∷ P 'PlainP → BaseVal → BaseType
  typeOf _p = typeOfBaseVal

  shareBaseVal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'PlainP → PrinVal → 𝑃 PrinVal → BaseVal → m BaseVal
  shareBaseVal _p _ρv _ρvs = return

  shareUnk ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'PlainP → PrinVal → 𝑃 PrinVal → BaseType → m BaseVal
  shareUnk _p _ρv _ρvs _bτ = throwIErrorCxt NotImplementedIError "[PlainP] exeUnk: TODO" empty𝐿

  embedBaseVal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'PlainP → 𝑃 PrinVal → BaseVal → m BaseVal
  embedBaseVal _p _ρvs = return

  exePrim ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'PlainP → 𝑃 PrinVal → Op → 𝐿 BaseVal → m BaseVal
  exePrim _p _ρvs = interpPrim

  reveal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'PlainP → 𝑃 PrinVal → PrinVal → MPCVal 'PlainP → m Val
  reveal p ρvs₁ ρv₂ v̂ =
    let toValP = SSecVP (SecM $ single𝑃 ρv₂) in
    case v̂ of
      DefaultMV    → return DefaultV
      BulMV        → return BulV
      BaseMV bv    → return $ BaseV bv
      PairMV v̂₁ v̂₂ → do
        v₁ ← reveal p ρvs₁ ρv₂ v̂₁
        v₂ ← reveal p ρvs₁ ρv₂ v̂₂
        return $ PairV (toValP v₁) (toValP v₂)
      SumMV bv₁ v̂₂ v̂₃ → do
        b₁ ← error𝑂 (view boolBVL bv₁) (throwIErrorCxt TypeIError "reveal: (view boolBVL bv₁) ≡ None" $ frhs
                                        [ ("bv₁", pretty bv₁)
                                        ])
        let inj :* v = if b₁ then LV :* (reveal p ρvs₁ ρv₂ v̂₂) else RV :* (reveal p ρvs₁ ρv₂ v̂₃)
        map (inj ∘ toValP) v
