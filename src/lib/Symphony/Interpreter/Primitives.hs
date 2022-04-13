module Symphony.Interpreter.Primitives where

import Symphony.Prelude

import Symphony.Interpreter.Types
import Symphony.Interpreter.BaseVal
import Symphony.Interpreter.Truncating
import Symphony.Interpreter.Pretty ()
import Symphony.Interpreter.Lens ()
import Symphony.Syntax
import Symphony.Interpreter.Error

primType ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, STACK) ⇒ Op → 𝐿 BaseType → m BaseType
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
  _ → throwIErrorCxt NotImplementedIError "bad" $ frhs [ ("op", pretty op), ("τs", pretty τs) ]

evalPrimClearBaseVal ∷ (Monad m, MonadReader (ICxt v) m, MonadError IError m, STACK) ⇒ Op → 𝐿 ClearBaseVal → m ClearBaseVal
evalPrimClearBaseVal o vs = case (o,tohs vs) of
  (OrO     ,[BoolV b₁, BoolV b₂])                   → return $ BoolV    $ b₁ ⩔ b₂
  (PlusO   ,[NatV pr₁ n₁, NatV pr₂ n₂]) | pr₁ ≡ pr₂ → return $ NatV pr₁ $ trPrNat pr₁ $ n₁ + n₂
  (PlusO   ,[IntV pr₁ i₁, IntV pr₂ i₂]) | pr₁ ≡ pr₂ → return $ IntV pr₁ $ trPrInt pr₁ $ i₁ + i₂
  (AndO    ,[BoolV b₁  ,BoolV b₂  ])                → return $ BoolV   $ b₁ ⩓ b₂
  (NotO    ,[BoolV b])                              → return $ BoolV   $ not b
  (PlusO   ,[BoolV b₁  ,BoolV b₂  ])                → return $ BoolV   $ b₁ ⩔ b₂
  (PlusO   ,[NatV p₁ n₁,NatV p₂ n₂])         |p₁≡p₂→ return $ NatV p₁ $ trPrNat p₁ $ n₁ + n₂
  (PlusO   ,[IntV p₁ i₁,IntV p₂ i₂])         |p₁≡p₂→ return $ IntV p₁ $ trPrInt p₁ $ i₁ + i₂
  (PlusO   ,[FltV p₁ f₁,FltV p₂ f₂])         |p₁≡p₂→ return $ FltV p₁ $ f₁ + f₂
  (PlusO   ,[PrinSetV ρvs₁, PrinSetV ρvs₂])        → return $ PrinSetV $ PowPSV $ (elimPSV ρvs₁) ∪ (elimPSV ρvs₂)
  (MinusO  ,[NatV p₁ n₁,NatV p₂ n₂])         |p₁≡p₂→ return $ NatV p₁ $ trPrNat p₁ $ buPrNat p₁ n₁ - n₂
  (MinusO  ,[IntV p₁ i₁,IntV p₂ i₂])         |p₁≡p₂→ return $ IntV p₁ $ trPrInt p₁ $ i₁ - i₂
  (MinusO  ,[FltV p₁ f₁,FltV p₂ f₂])         |p₁≡p₂→ return $ FltV p₁ $ f₁ - f₂
  (TimesO  ,[NatV p₁ n₁,NatV p₂ n₂])         |p₁≡p₂→ return $ NatV p₁ $ trPrNat p₁ $ n₁ × n₂
  (TimesO  ,[IntV p₁ i₁,IntV p₂ i₂])         |p₁≡p₂→ return $ IntV p₁ $ trPrInt p₁ $ i₁ × i₂
  (TimesO  ,[FltV p₁ f₁,FltV p₂ f₂])         |p₁≡p₂→ return $ FltV p₁ $ f₁ × f₂
  (ExpO    ,[NatV p₁ n₁,NatV p₂ n₂])         |p₁≡p₂→ return $ NatV p₁ $ trPrNat p₁ $ n₁ ^^ n₂
  (ExpO    ,[IntV p₁ i₁,NatV p₂ n₂])         |p₁≡p₂→ return $ IntV p₁ $ trPrInt p₁ $ i₁ ^^ n₂
  (ExpO    ,[FltV p₁ f₁,FltV p₂ f₂])         |p₁≡p₂→ return $ FltV p₁ $ f₁ ^ f₂
  (DivO    ,[NatV p₁ n₁,NatV p₂ n₂])         |p₁≡p₂→ return $ NatV p₁ $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ⌿ n₂
  (DivO    ,[IntV p₁ i₁,IntV p₂ i₂])         |p₁≡p₂→ return $ IntV p₁ $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ⌿ i₂
  (DivO    ,[FltV p₁ f₁,FltV p₂ f₂])         |p₁≡p₂→ return $ FltV p₁ $              if f₂ ≡ 0.0   then f₁ else f₁ / f₂
  (ModO    ,[NatV p₁ n₁,NatV p₂ n₂])         |p₁≡p₂→ return $ NatV p₁ $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ÷ n₂
  (ModO    ,[IntV p₁ i₁,IntV p₂ i₂])         |p₁≡p₂→ return $ IntV p₁ $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ÷ i₂
  (EqO     ,[BoolV b₁  ,BoolV b₂  ])               → return $ BoolV   $ b₁ ≡ b₂
  (EqO     ,[NatV p₁ n₁,NatV p₂ n₂])         |p₁≡p₂→ return $ BoolV   $ n₁ ≡ n₂
  (EqO     ,[IntV p₁ i₁,IntV p₂ i₂])         |p₁≡p₂→ return $ BoolV   $ i₁ ≡ i₂
  (EqO     ,[FltV p₁ f₁,FltV p₂ f₂])         |p₁≡p₂→ return $ BoolV   $ f₁ ≡ f₂
  (EqO     ,[PrinV ρev₁, PrinV ρev₂])              → return $ BoolV   $ ρev₁ ≡ ρev₂
  (LTO     ,[NatV p₁ n₁,NatV p₂ n₂])         |p₁≡p₂→ return $ BoolV   $ n₁ < n₂
  (LTO     ,[IntV p₁ i₁,IntV p₂ i₂])         |p₁≡p₂→ return $ BoolV   $ i₁ < i₂
  (LTO     ,[FltV p₁ f₁,FltV p₂ f₂])         |p₁≡p₂→ return $ BoolV   $ f₁ < f₂
  (GTO     ,[NatV p₁ n₁,NatV p₂ n₂])         |p₁≡p₂→ return $ BoolV   $ n₁ > n₂
  (GTO     ,[IntV p₁ i₁,IntV p₂ i₂])         |p₁≡p₂→ return $ BoolV   $ i₁ > i₂
  (GTO     ,[FltV p₁ f₁,FltV p₂ f₂])         |p₁≡p₂→ return $ BoolV   $ f₁ > f₂
  (LTEO    ,[NatV p₁ n₁,NatV p₂ n₂])         |p₁≡p₂→ return $ BoolV   $ n₁ ≤ n₂
  (LTEO    ,[IntV p₁ i₁,IntV p₂ i₂])         |p₁≡p₂→ return $ BoolV   $ i₁ ≤ i₂
  (LTEO    ,[FltV p₁ f₁,FltV p₂ f₂])         |p₁≡p₂→ return $ BoolV   $ f₁ ≤ f₂
  (GTEO    ,[NatV p₁ n₁,NatV p₂ n₂])         |p₁≡p₂→ return $ BoolV   $ n₁ ≥ n₂
  (GTEO    ,[IntV p₁ i₁,IntV p₂ i₂])         |p₁≡p₂→ return $ BoolV   $ i₁ ≥ i₂
  (GTEO    ,[FltV p₁ f₁,FltV p₂ f₂])         |p₁≡p₂→ return $ BoolV   $ f₁ ≥ f₂
  (CondO   ,[BoolV b,BoolV b₁  ,BoolV b₂  ])      → return $ BoolV   $ if b then b₁ else b₂
  (CondO   ,[BoolV b,NatV p₁ n₁,NatV p₂ n₂])|p₁≡p₂→ return $ NatV p₁ $ if b then n₁ else n₂
  (CondO   ,[BoolV b,IntV p₁ i₁,IntV p₂ i₂])|p₁≡p₂→ return $ IntV p₁ $ if b then i₁ else i₂
  (CondO   ,[BoolV b,FltV p₁ f₁,FltV p₂ f₂])|p₁≡p₂→ return $ FltV p₁ $ if b then f₁ else f₂
  (AbsO    ,[IntV p i])                             → return $ NatV p  $ zabs i
  (LogO    ,[FltV p f])                             → return $ FltV p  $ logBase 2.0 f
  (SqrtO   ,[FltV p f])                             → return $ FltV p  $ root f
  (NatO p₁ ,[NatV _ n])                            → return $ NatV p₁ $ trPrNat p₁ n
  (NatO p₁ ,[IntV _ i])                            → return $ NatV p₁ $ trPrNat p₁ $ natΩ i
  (IntO p₁ ,[IntV _ i])                            → return $ IntV p₁ $ trPrInt p₁ i
  (IntO p₁ ,[NatV _ n])                            → return $ IntV p₁ $ trPrInt p₁ $ int n
  (FltO p₁ ,[NatV _ n])                            → return $ FltV p₁ $ dbl n
  (FltO p₁ ,[IntV _ i])                            → return $ FltV p₁ $ dbl i
  (FltO p₁ ,[FltV _ d])                            → return $ FltV p₁ $ d
  (CeilO p₁,[FltV _ f])                            → return $ IntV p₁ $ ceiling f
  _ → throwIErrorCxt NotImplementedIError "interpPrim" $ frhs
    [ ("o",pretty o)
    , ("vs",pretty vs)
    ]
