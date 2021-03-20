module PSL.Interpreter.Primitives where

import UVMHS

import PSL.Interpreter.Types
import PSL.Interpreter.Truncating
import PSL.Interpreter.Pretty ()
import PSL.Syntax
import PSL.Interpreter.Json ()
import PSL.Interpreter.Error

import AddToUVMHS

primType ∷ (STACK) ⇒ Op → 𝐿 Type → IM Type
primType op τs = case (op, tohs τs) of
  (OrO, [𝔹T, 𝔹T]) → return 𝔹T
  (PlusO, [ℕT pr₁, ℕT pr₂]) | pr₁ ≡ pr₂ → return $ ℕT pr₁
  (PlusO, [ℤT pr₁, ℤT pr₂]) | pr₁ ≡ pr₂ → return $ ℤT pr₁
  (ExpO, [𝔽T pr₁, 𝔽T pr₂]) | pr₁ ≡ pr₂ → return $ 𝔽T pr₁
  (CondO, [𝔹T, ℤT pr₁, ℤT pr₂]) | pr₁ ≡ pr₂ → return $ ℤT pr₁
  _ → throwIErrorCxt NotImplementedIError "primType" $ frhs
    [ ("op", pretty op)
    , ("τs", pretty τs)
    ]

interpPrim ∷ (STACK) ⇒ Op → 𝐿 BaseVal → IM BaseVal
interpPrim o vs = case (o,tohs vs) of
  (OrO     ,[BoolBV b₁, BoolBV b₂])                   → return $ BoolBV    $ b₁ ⩔ b₂
  (PlusO   ,[NatBV pr₁ n₁, NatBV pr₂ n₂]) | pr₁ ≡ pr₂ → return $ NatBV pr₁ $ trPrNat pr₁ $ n₁ + n₂
  (PlusO   ,[IntBV pr₁ i₁, IntBV pr₂ i₂]) | pr₁ ≡ pr₂ → return $ IntBV pr₁ $ trPrInt pr₁ $ i₁ + i₂
  (ExpO    ,[FltBV pr₁ f₁, FltBV pr₂ f₂]) | pr₁ ≡ pr₂ → return $ FltBV pr₁ $ f₁ ^ f₂
  (AndO    ,[BoolBV b₁  ,BoolBV b₂  ])                → return $ BoolBV   $ b₁ ⩓ b₂
  (NotO    ,[BoolBV b])                              → return $ BoolBV   $ not b
  (PlusO   ,[BoolBV b₁  ,BoolBV b₂  ])                → return $ BoolBV   $ b₁ ⩔ b₂
  (PlusO   ,[NatBV p₁ n₁,NatBV p₂ n₂])          |p₁≡p₂→ return $ NatBV p₁ $ trPrNat p₁ $ n₁ + n₂
  (PlusO   ,[IntBV p₁ i₁,IntBV p₂ i₂])         |p₁≡p₂→ return $ IntBV p₁ $ trPrInt p₁ $ i₁ + i₂
  (PlusO   ,[FltBV p₁ f₁,FltBV p₂ f₂])         |p₁≡p₂→ return $ FltBV p₁ $ f₁ + f₂
  (PlusO   ,[PrinBV (ValPEV ρv₁)  ,PrinBV (ValPEV ρv₂)  ])               → case (AddBTD ρv₁) ⊔ (AddBTD ρv₂) of
                                                                                    BotBTD → impossible
                                                                                    AddBTD ρv → return $ PrinBV $ ValPEV ρv
                                                                                    TopBTD → return $ BulBV
  (MinusO  ,[NatBV p₁ n₁,NatBV p₂ n₂])         |p₁≡p₂→ return $ NatBV p₁ $ trPrNat p₁ $ buPrNat p₁ n₁ - n₂
  (MinusO  ,[IntBV p₁ i₁,IntBV p₂ i₂])         |p₁≡p₂→ return $ IntBV p₁ $ trPrInt p₁ $ i₁ - i₂
  (MinusO  ,[FltBV p₁ f₁,FltBV p₂ f₂])         |p₁≡p₂→ return $ FltBV p₁ $ f₁ - f₂
  (TimesO  ,[NatBV p₁ n₁,NatBV p₂ n₂])         |p₁≡p₂→ return $ NatBV p₁ $ trPrNat p₁ $ n₁ × n₂
  (TimesO  ,[IntBV p₁ i₁,IntBV p₂ i₂])         |p₁≡p₂→ return $ IntBV p₁ $ trPrInt p₁ $ i₁ × i₂
  (TimesO  ,[FltBV p₁ f₁,FltBV p₂ f₂])         |p₁≡p₂→ return $ FltBV p₁ $ f₁ × f₂
  (ExpO    ,[NatBV p₁ n₁,NatBV p₂ n₂])         |p₁≡p₂→ return $ NatBV p₁ $ trPrNat p₁ $ n₁ ^^ n₂
  (ExpO    ,[IntBV p₁ i₁,NatBV p₂ n₂])         |p₁≡p₂→ return $ IntBV p₁ $ trPrInt p₁ $ i₁ ^^ n₂
  (ExpO    ,[FltBV p₁ f₁,FltBV p₂ f₂])         |p₁≡p₂→ return $ FltBV p₁ $ f₁ ^ f₂
  (DivO    ,[NatBV p₁ n₁,NatBV p₂ n₂])         |p₁≡p₂→ return $ NatBV p₁ $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ⌿ n₂
  (DivO    ,[IntBV p₁ i₁,IntBV p₂ i₂])         |p₁≡p₂→ return $ IntBV p₁ $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ⌿ i₂
  (DivO    ,[FltBV p₁ f₁,FltBV p₂ f₂])         |p₁≡p₂→ return $ FltBV p₁ $              if f₂ ≡ 0.0   then f₁ else f₁ / f₂
  (ModO    ,[NatBV p₁ n₁,NatBV p₂ n₂])         |p₁≡p₂→ return $ NatBV p₁ $ trPrNat p₁ $ if n₂ ≡ 0     then n₁ else n₁ ÷ n₂
  (ModO    ,[IntBV p₁ i₁,IntBV p₂ i₂])         |p₁≡p₂→ return $ IntBV p₁ $ trPrInt p₁ $ if i₂ ≡ int 0 then i₁ else i₁ ÷ i₂
  (EqO     ,[BoolBV b₁  ,BoolBV b₂  ])               → return $ BoolBV   $ b₁ ≡ b₂
  (EqO     ,[NatBV p₁ n₁,NatBV p₂ n₂])         |p₁≡p₂→ return $ BoolBV   $ n₁ ≡ n₂
  (EqO     ,[IntBV p₁ i₁,IntBV p₂ i₂])         |p₁≡p₂→ return $ BoolBV   $ i₁ ≡ i₂
  (EqO     ,[FltBV p₁ f₁,FltBV p₂ f₂])         |p₁≡p₂→ return $ BoolBV   $ f₁ ≡ f₂
  (EqO     ,[PrinBV ρev₁,PrinBV ρev₂])               → return $ BoolBV   $ ρev₁ ≡ ρev₂
  (LTO     ,[NatBV p₁ n₁,NatBV p₂ n₂])         |p₁≡p₂→ return $ BoolBV   $ n₁ < n₂
  (LTO     ,[IntBV p₁ i₁,IntBV p₂ i₂])         |p₁≡p₂→ return $ BoolBV   $ i₁ < i₂
  (LTO     ,[FltBV p₁ f₁,FltBV p₂ f₂])         |p₁≡p₂→ return $ BoolBV   $ f₁ < f₂
  (GTO     ,[NatBV p₁ n₁,NatBV p₂ n₂])         |p₁≡p₂→ return $ BoolBV   $ n₁ > n₂
  (GTO     ,[IntBV p₁ i₁,IntBV p₂ i₂])         |p₁≡p₂→ return $ BoolBV   $ i₁ > i₂
  (GTO     ,[FltBV p₁ f₁,FltBV p₂ f₂])         |p₁≡p₂→ return $ BoolBV   $ f₁ > f₂
  (LTEO    ,[NatBV p₁ n₁,NatBV p₂ n₂])         |p₁≡p₂→ return $ BoolBV   $ n₁ ≤ n₂
  (LTEO    ,[IntBV p₁ i₁,IntBV p₂ i₂])         |p₁≡p₂→ return $ BoolBV   $ i₁ ≤ i₂
  (LTEO    ,[FltBV p₁ f₁,FltBV p₂ f₂])         |p₁≡p₂→ return $ BoolBV   $ f₁ ≤ f₂
  (GTEO    ,[NatBV p₁ n₁,NatBV p₂ n₂])         |p₁≡p₂→ return $ BoolBV   $ n₁ ≥ n₂
  (GTEO    ,[IntBV p₁ i₁,IntBV p₂ i₂])         |p₁≡p₂→ return $ BoolBV   $ i₁ ≥ i₂
  (GTEO    ,[FltBV p₁ f₁,FltBV p₂ f₂])         |p₁≡p₂→ return $ BoolBV   $ f₁ ≥ f₂
  (CondO   ,[BoolBV b,BoolBV b₁  ,BoolBV b₂  ])      → return $ BoolBV   $ if b then b₁ else b₂
  (CondO   ,[BoolBV b,NatBV p₁ n₁,NatBV p₂ n₂])|p₁≡p₂→ return $ NatBV p₁ $ if b then n₁ else n₂
  (CondO   ,[BoolBV b,IntBV p₁ i₁,IntBV p₂ i₂])|p₁≡p₂→ return $ IntBV p₁ $ if b then i₁ else i₂
  (CondO   ,[BoolBV b,FltBV p₁ f₁,FltBV p₂ f₂])|p₁≡p₂→ return $ FltBV p₁ $ if b then f₁ else f₂
  (CondO   ,[BoolBV b,PrinBV p₁  ,PrinBV p₂  ])      → return $ PrinBV   $ if b then p₁ else p₂
  (AbsO    ,[IntBV p i])                             → return $ NatBV p  $ zabs i
  (LogO    ,[FltBV p f])                             → return $ FltBV p  $ logBase 2.0 f
  (SqrtO   ,[FltBV p f])                             → return $ FltBV p  $ root f
  (NatO p₁ ,[NatBV _ n])                            → return $ NatBV p₁ $ trPrNat p₁ n
  (NatO p₁ ,[IntBV _ i])                            → return $ NatBV p₁ $ trPrNat p₁ $ natΩ i
  (IntO p₁ ,[IntBV _ i])                            → return $ IntBV p₁ $ trPrInt p₁ i
  (IntO p₁ ,[NatBV _ n])                            → return $ IntBV p₁ $ trPrInt p₁ $ int n
  (FltO p₁ ,[NatBV _ n])                            → return $ FltBV p₁ $ dbl n
  (FltO p₁ ,[IntBV _ i])                            → return $ FltBV p₁ $ dbl i
  (FltO p₁ ,[FltBV _ d])                            → return $ FltBV p₁ $ d
  (CeilO p₁,[FltBV _ f])                            → return $ IntBV p₁ $ ceiling f
  _ → throwIErrorCxt NotImplementedIError "interpPrim" $ frhs
    [ ("o",pretty o)
    , ("vs",pretty vs)
    ]
