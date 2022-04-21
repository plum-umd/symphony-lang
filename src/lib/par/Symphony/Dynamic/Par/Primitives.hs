module Symphony.Dynamic.Par.Primitives where

import Symphony.Prelude

import Symphony.Lang.Syntax

import Symphony.Dynamic.Par.Types
import Symphony.Dynamic.Par.Truncating
import Symphony.Dynamic.Par.Error

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
  (OrO     ,[BoolCV b₁, BoolCV b₂])                   → return $ BoolCV    $ b₁ ⩔ b₂
  (PlusO   ,[NatCV pr₁ n₁, NatCV pr₂ n₂]) | pr₁ ≡ pr₂ → return $ NatCV pr₁ $ trPrNat pr₁ $ n₁ + n₂
  (PlusO   ,[IntCV pr₁ i₁, IntCV pr₂ i₂]) | pr₁ ≡ pr₂ → return $ IntCV pr₁ $ trPrInt pr₁ $ i₁ + i₂
  (AndO    ,[BoolCV b₁  ,BoolCV b₂  ])                → return $ BoolCV   $ b₁ ⩓ b₂
  (NotO    ,[BoolCV b])                              → return $ BoolCV   $ not b
  (PlusO   ,[BoolCV b₁  ,BoolCV b₂  ])                → return $ BoolCV   $ b₁ ⩔ b₂
  (PlusO   ,[NatCV p₁ n₁,NatCV p₂ n₂])         |p₁≡p₂→ return $ NatCV p₁ $ trPrNat p₁ $ n₁ + n₂
  (PlusO   ,[IntCV p₁ i₁,IntCV p₂ i₂])         |p₁≡p₂→ return $ IntCV p₁ $ trPrInt p₁ $ i₁ + i₂
  (PlusO   ,[FltCV p₁ f₁,FltCV p₂ f₂])         |p₁≡p₂→ return $ FltCV p₁ $ f₁ + f₂
  (PlusO   ,[PrinSetCV ρvs₁, PrinSetCV ρvs₂])        → return $ PrinSetCV $ PowPSV $ (elimPSV ρvs₁) ∪ (elimPSV ρvs₂)
  (MinusO  ,[NatCV p₁ n₁,NatCV p₂ n₂])         |p₁≡p₂→ return $ NatCV p₁ $ trPrNat p₁ $ buPrNat p₁ n₁ - n₂
  (MinusO  ,[IntCV p₁ i₁,IntCV p₂ i₂])         |p₁≡p₂→ return $ IntCV p₁ $ trPrInt p₁ $ i₁ - i₂
  (MinusO  ,[FltCV p₁ f₁,FltCV p₂ f₂])         |p₁≡p₂→ return $ FltCV p₁ $ f₁ - f₂
  (TimesO  ,[NatCV p₁ n₁,NatCV p₂ n₂])         |p₁≡p₂→ return $ NatCV p₁ $ trPrNat p₁ $ n₁ × n₂
  (TimesO  ,[IntCV p₁ i₁,IntCV p₂ i₂])         |p₁≡p₂→ return $ IntCV p₁ $ trPrInt p₁ $ i₁ × i₂
  (TimesO  ,[FltCV p₁ f₁,FltCV p₂ f₂])         |p₁≡p₂→ return $ FltCV p₁ $ f₁ × f₂
  (ExpO    ,[NatCV p₁ n₁,NatCV p₂ n₂])         |p₁≡p₂→ return $ NatCV p₁ $ trPrNat p₁ $ n₁ ^^ n₂
  (ExpO    ,[IntCV p₁ i₁,NatCV p₂ n₂])         |p₁≡p₂→ return $ IntCV p₁ $ trPrInt p₁ $ i₁ ^^ n₂
  (ExpO    ,[FltCV p₁ f₁,FltCV p₂ f₂])         |p₁≡p₂→ return $ FltCV p₁ $ f₁ ^ f₂
  (DivO    ,[NatCV p₁ n₁,NatCV p₂ n₂])         |p₁≡p₂→ return $ NatCV p₁ $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ⌿ n₂
  (DivO    ,[IntCV p₁ i₁,IntCV p₂ i₂])         |p₁≡p₂→ return $ IntCV p₁ $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ⌿ i₂
  (DivO    ,[FltCV p₁ f₁,FltCV p₂ f₂])         |p₁≡p₂→ return $ FltCV p₁ $              if f₂ ≡ 0.0   then f₁ else f₁ / f₂
  (ModO    ,[NatCV p₁ n₁,NatCV p₂ n₂])         |p₁≡p₂→ return $ NatCV p₁ $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ÷ n₂
  (ModO    ,[IntCV p₁ i₁,IntCV p₂ i₂])         |p₁≡p₂→ return $ IntCV p₁ $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ÷ i₂
  (EqO     ,[BoolCV b₁  ,BoolCV b₂  ])               → return $ BoolCV   $ b₁ ≡ b₂
  (EqO     ,[NatCV p₁ n₁,NatCV p₂ n₂])         |p₁≡p₂→ return $ BoolCV   $ n₁ ≡ n₂
  (EqO     ,[IntCV p₁ i₁,IntCV p₂ i₂])         |p₁≡p₂→ return $ BoolCV   $ i₁ ≡ i₂
  (EqO     ,[FltCV p₁ f₁,FltCV p₂ f₂])         |p₁≡p₂→ return $ BoolCV   $ f₁ ≡ f₂
  (EqO     ,[PrinCV ρev₁, PrinCV ρev₂])              → return $ BoolCV   $ ρev₁ ≡ ρev₂
  (LTO     ,[NatCV p₁ n₁,NatCV p₂ n₂])         |p₁≡p₂→ return $ BoolCV   $ n₁ < n₂
  (LTO     ,[IntCV p₁ i₁,IntCV p₂ i₂])         |p₁≡p₂→ return $ BoolCV   $ i₁ < i₂
  (LTO     ,[FltCV p₁ f₁,FltCV p₂ f₂])         |p₁≡p₂→ return $ BoolCV   $ f₁ < f₂
  (GTO     ,[NatCV p₁ n₁,NatCV p₂ n₂])         |p₁≡p₂→ return $ BoolCV   $ n₁ > n₂
  (GTO     ,[IntCV p₁ i₁,IntCV p₂ i₂])         |p₁≡p₂→ return $ BoolCV   $ i₁ > i₂
  (GTO     ,[FltCV p₁ f₁,FltCV p₂ f₂])         |p₁≡p₂→ return $ BoolCV   $ f₁ > f₂
  (LTEO    ,[NatCV p₁ n₁,NatCV p₂ n₂])         |p₁≡p₂→ return $ BoolCV   $ n₁ ≤ n₂
  (LTEO    ,[IntCV p₁ i₁,IntCV p₂ i₂])         |p₁≡p₂→ return $ BoolCV   $ i₁ ≤ i₂
  (LTEO    ,[FltCV p₁ f₁,FltCV p₂ f₂])         |p₁≡p₂→ return $ BoolCV   $ f₁ ≤ f₂
  (GTEO    ,[NatCV p₁ n₁,NatCV p₂ n₂])         |p₁≡p₂→ return $ BoolCV   $ n₁ ≥ n₂
  (GTEO    ,[IntCV p₁ i₁,IntCV p₂ i₂])         |p₁≡p₂→ return $ BoolCV   $ i₁ ≥ i₂
  (GTEO    ,[FltCV p₁ f₁,FltCV p₂ f₂])         |p₁≡p₂→ return $ BoolCV   $ f₁ ≥ f₂
  (CondO   ,[BoolCV b,BoolCV b₁  ,BoolCV b₂  ])      → return $ BoolCV   $ if b then b₁ else b₂
  (CondO   ,[BoolCV b,NatCV p₁ n₁,NatCV p₂ n₂])|p₁≡p₂→ return $ NatCV p₁ $ if b then n₁ else n₂
  (CondO   ,[BoolCV b,IntCV p₁ i₁,IntCV p₂ i₂])|p₁≡p₂→ return $ IntCV p₁ $ if b then i₁ else i₂
  (CondO   ,[BoolCV b,FltCV p₁ f₁,FltCV p₂ f₂])|p₁≡p₂→ return $ FltCV p₁ $ if b then f₁ else f₂
  (AbsO    ,[IntCV p i])                             → return $ NatCV p  $ zabs i
  (LogO    ,[FltCV p f])                             → return $ FltCV p  $ logBase 2.0 f
  (SqrtO   ,[FltCV p f])                             → return $ FltCV p  $ root f
  (NatO p₁ ,[NatCV _ n])                            → return $ NatCV p₁ $ trPrNat p₁ n
  (NatO p₁ ,[IntCV _ i])                            → return $ NatCV p₁ $ trPrNat p₁ $ natΩ i
  (IntO p₁ ,[IntCV _ i])                            → return $ IntCV p₁ $ trPrInt p₁ i
  (IntO p₁ ,[NatCV _ n])                            → return $ IntCV p₁ $ trPrInt p₁ $ int n
  (FltO p₁ ,[NatCV _ n])                            → return $ FltCV p₁ $ dbl n
  (FltO p₁ ,[IntCV _ i])                            → return $ FltCV p₁ $ dbl i
  (FltO p₁ ,[FltCV _ d])                            → return $ FltCV p₁ $ d
  (CeilO p₁,[FltCV _ f])                            → return $ IntCV p₁ $ ceiling f
  _ → throwIErrorCxt NotImplementedIError "interpPrim" $ frhs
    [ ("o",pretty o)
    , ("vs",pretty vs)
    ]
