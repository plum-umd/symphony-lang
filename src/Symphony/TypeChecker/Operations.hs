module Symphony.TypeChecker.Operations where

import UVMHS
import AddToUVMHS

import Symphony.Syntax
import Symphony.TypeChecker.Error
import Symphony.TypeChecker.TLM hiding (TLR)
import Symphony.TypeChecker.EM
import Symphony.TypeChecker.Env

-----------------
--- Primitives ---
-----------------

-- Takes an op, list of base types, and returns what the op should return on the base type
primType ∷ STACK ⇒ Op → 𝐿 BaseType → EM BaseType
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
  _ → todoError

-- Gets protocol of located type
extractProt :: STACK ⇒ Type → EM (𝑂 (Prot, ModeAny) )
extractProt τ =
 case τ of
  (SecT _  (ShareT p loc _))   → do
    l ← elabEMode loc
    return (Some (p, l))
  (SecT _ _)  → return None
  _ →   typeError "ExtractProt: τ is mot well formed type" $ frhs
                  [ ("τ", pretty τ)
                  ]

assertM :: STACK ⇒ ModeAny → Type → EM ()
assertM m τ =
  case τ of
    (SecT loc _)  →  do
          l ← elabEMode loc
          guardErr (eq_mode m l)  $
            typeError "ExtractProt: m != l" $ frhs
                  [ ("m", pretty m)
                  , ("l", pretty l)
                  ]
          return ()
    _  → typeError "AssertM: τ is not well formed type" $ frhs
                  [ ("τ", pretty τ)
                  ]


-- Extracts basetype
extractBase :: STACK ⇒ Type → EM BaseType
extractBase τ =
   case τ of
     (SecT _ (BaseT bτ))  → return bτ
     (SecT _ (ShareT _ _ (BaseT bτ)))  →  return bτ
     _ → typeError "ExtractProt: τ is not a well formed base type" $ frhs
                  [ ("τ", pretty τ)
                  ]

-- Assumes it is either a share OR a cleartext that shareable
embedShare :: STACK ⇒  Prot → EMode → Type → EM Type
embedShare φ l τ =
    case τ of
    (SecT l' sigma) → 
      case sigma of
        (ShareT _ _ _) → return τ
        (BaseT bτ)  → return (SecT l' (ShareT φ l (BaseT bτ)))
        (τₗ :+: τᵣ)  →  do
          τₗ' ← (embedShare φ l τₗ )
          τᵣ' ← (embedShare φ l τᵣ )
          return (SecT l' (ShareT φ l (τₗ' :+: τᵣ')))
        (τₗ :×:  τᵣ)  →  do
          τₗ' ← (embedShare φ l τₗ )
          τᵣ' ← (embedShare φ l τᵣ )
          return (SecT l' (ShareT φ l (τₗ' :+: τᵣ')))
        (ListT n τₜ)  →   do
          τₜ' ← (embedShare φ l τₜ)
          return (SecT l' (ShareT φ l (ListT n τₜ') ))
        _ → typeError "EmbedShare: τ is not a well type" $ frhs
                  [ ("τ", pretty τ)
                  ]
    _ → typeError "EmbedShare: τ is not a well type" $ frhs
                  [ ("τ", pretty τ)
                  ]

-- If it's well formed, the first two are uncessary



{-
embedShare :: STACK ⇒  Prot → EMode → Type → EM Type
embedShare φ l τ =
  case τ of
    (SecT l' (ShareT φ' l'' (BaseT bτ))) → do
      q ← elabEMode l
      q'' ← elabEMode l''
      guardErr ((q ≡ q'') ⩓ φ ≡ φ') $
        typeError "Not well formed q != w'" $ frhs
        [ ("q", pretty q)
        , ("w", pretty q'')
        ]
      return (SecT l' (ShareT φ l (BaseT bτ)))
    (SecT l' (BaseT bτ))  → return (SecT l' (ShareT φ l (BaseT bτ)))
    (SecT l' (ShareT φ' l'' (τₗ :+: τᵣ))) → do
      q ← elabEMode l
      q'' ← elabEMode l''
      guardErr ((q ≡ q'') ⩓ φ ≡ φ) $
        todoError
      τₗ' ← (embedShare φ l τₗ )
      τᵣ' ← (embedShare φ l τᵣ )
      return (SecT l' (ShareT φ l (τₗ' :+: τᵣ')))
    (SecT l' (τₗ :+: τᵣ) )  → do
      τₗ' ← (embedShare φ l τₗ )
      τᵣ' ← (embedShare φ l τᵣ )
      return (SecT l' (ShareT φ l (τₗ' :+: τᵣ')))
    _ → todoError
-}

-- Asserts it is shareable (only Cleartext)
isEmbedable :: STACK ⇒   Type → 𝔹
isEmbedable τ =
  case τ of
    (SecT l' sigma) → 
      case sigma of
        (BaseT bτ)  → True
        (τₗ :+: τᵣ)  → (isEmbedable τₗ ) ⩓ (isEmbedable τᵣ )
        (τₗ :×:  τᵣ)  → (isEmbedable τₗ ) ⩓ (isEmbedable τᵣ )
        (ListT _ τₜ)  →  (isEmbedable τₜ ) 
        _ → False
    _ → False

-- Asserts it is shareable (only Cleartext)
isShared :: STACK ⇒   Type → 𝔹
isShared τ =
  case τ of
    (SecT _  (ShareT _ _ _) ) → True
    _ → False

assertShareable  :: STACK ⇒   Type → EM ()
assertShareable τ = do
    guardErr ((isEmbedable τ) ⩔ (isShared τ)) $
      typeError "assertShareable: τ is not '" $ frhs
      [ ("τ", pretty τ)
      ]
    return ()

eModeEqual :: STACK ⇒ EMode → EMode → EM 𝔹
eModeEqual loc loc' =
  do
    p ←  elabEMode loc
    p' ← elabEMode loc'
    return $ eq_mode p p'


-----------------
--- Subtype utility ---
-----------------

-- Check if loctyS <: loctyT
subtype_loc :: STACK ⇒ Type → Type →  𝑃 (TVar, TVar)  → EM 𝔹
subtype_loc loctyS loctyT d = case loctyS of
  -- sigma = bty
  -- -------Sub-Refl
  -- sigma <: sigma
  -- sigma = bty^phi
  -- -------Sub-Refl
  -- sigma <: sigma
  BaseT bty → return (loctyS ≡ loctyT)
  ShareT pS loc loctyS  → case loctyT of
      ShareT pT loc' loctyT → do
        l ← (elabEMode loc)
        l' ← (elabEMode loc')
        loccond ← (subtype_loc loctyS loctyT d)
        return ((eq_mode l l') ⩓ (pS ≡ pT) ⩓ loccond)
      _  → return False
  -- t1 <: t1' t2 <: t2'
  -- -------Sub-Sum
  -- t1 + t2 <: t1' + t2'
  (loctySₗ :+: loctySᵣ) → case loctyT of
    (loctyTₗ :+: loctyTᵣ) → do

        loccondₗ ← (subtype loctySₗ loctyTₗ d)
        loccondᵣ ← (subtype loctySᵣ loctyTᵣ d)
        return (loccondₗ ⩓ loccondᵣ)
    _ → return False
  -- t1 <: t1' t2 <: t2'
  -- -------Sub-Pair
  -- t1 x t2 <: t1' x t2'
  (loctySₗ :×: loctySᵣ) → case loctyT of
    (loctyTₗ :×: loctyTᵣ) → do
        loccondₗ ← (subtype loctySₗ loctyTₗ d)
        loccondᵣ ← (subtype loctySᵣ loctyTᵣ d)
        return (loccondₗ ⩓ loccondᵣ)
    _ → return False
  (ListT _ τₜ)  →  case loctyT of
    (ListT _ τₜ') → (subtype τₜ τₜ' d)
    _ → return False
  -- t1' <: t1 t2 <: t2'
  -- -------Sub-Fun
  -- t1 m -> t2 <: t1' m -> t2'
  (τ₁₁ :→: (η :* τ₁₂)) → case loctyT of
    (τ₁₁' :→: (η' :* τ₁₂')) → do
        l ← elabEMode $ effectMode η
        l' ← elabEMode $ effectMode η'
        loccondₗ ← (subtype τ₁₁' τ₁₁ d)
        loccondᵣ ← (subtype τ₁₂ τ₁₂' d) 
        return ((eq_mode l l') ⩓ loccondₗ ⩓ loccondᵣ)
        -- t <: t' 
  -- -------Sub-RefRO
  -- ref _ t <: ref RO t'
  (RefT None τ) →  case loctyT of
    (RefT None τ') → (subtype τ τ' d)
    _  → return False
  (RefT _ τ) → case loctyT of
      -- sigma = refRW#m t
    -- -------Sub-Refl
    -- sigma <: sigma
    (RefT None τ') → (subtype τ τ' d)
    _  → (eq_locty loctyS loctyT)
    -- -------Sub-RefRO
  -- ref _ t <: ref RO t
  (ArrT None _ τ) →  case loctyT of
    (ArrT None _ τ') → (subtype τ τ' d)
    _  → return False
  (ArrT _ _ τ) → case loctyT of
          -- sigma = refRW#m t
    -- -------Sub-Refl
    -- sigma <: sigma
    (ArrT None _ τ') → (subtype τ τ' d)
    _  → (eq_locty loctyS loctyT)
  ISecT locS loctyS  → case loctyT of
      ISecT locT loctyT → do
        mcond ← (superemode locS locT)
        loccond ← (subtype loctyS loctyT d)
        return (mcond ⩓ loccond)
  _ → return False

-- Check if tyS <: tyT
  -- d represents a set where if it contains (a,b) a = b or a <: b
subtype :: STACK ⇒ Type → Type → 𝑃 (TVar, TVar) →  EM 𝔹
subtype tyS tyT d = case tyS of
    -- sigma <: sigma' m ⊇ m'
  -- -------Sub-Loc
  -- sigma@m <: sigma'@m'
  SecT locS loctyS → case tyT of
      SecT locT loctyT → do
        mcond ← (superemode locS locT)
        loccond ← (subtype_loc loctyS loctyT d)
        return  (mcond ⩓ loccond)
      _ → return False
  VarT a → case tyT of
      VarT a' → do
        -- -------Sub-Var
         -- a <: a
         -- TODO: correct later
        return ((a ≡ a') ⩔ ( (a, a') ∈ d)) 
      _ → return False
  -- D, a <: b |- t1 <: t2
  -- --------------------------- Rec-Sub
  -- D |- mu a . t1 <: mu b . t2
  RecT a τ → case tyT of
      RecT a' τ' → do
        subcond ← (subtype τ τ' ((single𝑃  (a, a')) ∪ d))
        return ((a ≡ a') ⩓ subcond)
      _ → return False
  -- D, a = b |- t <: t'
  -- -------Sub-ForAll
  -- D |- forall a.t <: forall a.t'
  ForallT a τ → case tyT of
      ForallT a' τ' → do
        subcond ← (subtype τ τ' ((single𝑃  (a, a')) ∪ d))
        return ((a ≡ a') ⩓ subcond)
      _ → return False
  _ → return False


-- Check if tyT >: tyS
supertype :: STACK ⇒ Type → Type →  𝑃 (TVar, TVar)  → EM 𝔹
supertype tyT tyS = subtype tyS tyT

-- Checks if emT ⊇ emS
superemode :: STACK ⇒ EMode → EMode → EM 𝔹
superemode locT locS= do
  lT ← elabEMode locT
  lS ← elabEMode locS
  return (supermode lT lS)

-- Checks if mT ⊇ mS
supermode :: STACK ⇒ ModeAny → ModeAny → 𝔹
supermode locT locS = case locT of
  Any → True
  (AddAny Top) → True
  (AddAny (AddTop psT)) → case locS of
      Any → True
      (AddAny Top) → False
      (AddAny (AddTop psS)) → (psT ⊇ psS)

 -- Returns em ∩ em'
inter_em :: STACK ⇒ EMode → EMode → EM EMode
inter_em loc loc' = do
  l ← elabEMode loc
  l' ← elabEMode loc'
  (elabMode (inter_m l l'))

-- Returns m ∩ m'
inter_m :: STACK ⇒ ModeAny → ModeAny → ModeAny
inter_m l l' = case l of
  Any → Any
  (AddAny Top) → l'
  (AddAny (AddTop ps)) → case l' of
      Any → Any
      (AddAny Top) → (AddAny (AddTop ps))
      (AddAny (AddTop ps'))  → (AddAny (AddTop(ps ∩ ps')))

 -- Returns em ∩ em'
union_em :: STACK ⇒ EMode → EMode → EM EMode
union_em loc loc' = do
  l ← elabEMode loc
  l' ← elabEMode loc'
  (elabMode (union_m l l'))

-- Returns m ∩ m'
union_m :: STACK ⇒ ModeAny → ModeAny → ModeAny
union_m l l' = case l of
  Any → Any
  (AddAny Top) → case l' of
                  Any → Any
                  _ → (AddAny Top)
  (AddAny (AddTop ps)) → case l' of
      Any → Any
      (AddAny Top) → (AddAny Top)
      (AddAny (AddTop ps'))  → (AddAny (AddTop(ps ∪ ps')))

-- Checks if mT ⊇ mS
eq_mode :: STACK ⇒ ModeAny → ModeAny → 𝔹
eq_mode l l' = case l of
  Any → True
  (AddAny m) → case l' of
    Any  →  True
    (AddAny m') → m ≡  m'
      

-----------------
--- Join functions ---
-----------------
-- Checks if two located types are equal
eq_locty :: STACK ⇒ Type  → Type   →  EM 𝔹
eq_locty locty locty'=
  case locty of
    BaseT bty → return (locty ≡ locty') 
    ShareT p loc locty  → case locty' of
      ShareT p' loc' locty' → do
        l ← (elabEMode loc)
        l' ← (elabEMode loc')
        return ((p  ≡ p') ⩓ (eq_mode l l')) 
      _  → return False
    (tyₗ :+: tyᵣ) → case locty' of
      (ty'ₗ :+: ty'ᵣ) → do

        loccondₗ  ← (eq_type tyₗ ty'ₗ)
        loccondᵣ ← (eq_type tyᵣ ty'ᵣ)
        return (loccondₗ ⩓ loccondᵣ)
      _ →  return False

    (tyₗ :×: tyᵣ) → case locty' of
      (ty'ₗ :×: ty'ᵣ) → do

        loccondₗ  ← (eq_type tyₗ ty'ₗ)
        loccondᵣ ← (eq_type tyᵣ ty'ᵣ)
        return (loccondₗ ⩓ loccondᵣ)
      _ →   return False

    (ListT n τₜ)  →  case locty' of
      (ListT n' τₜ') → (eq_type τₜ τₜ')
      _ → return False
    (τ₁₁ :→: (η :* τ₁₂)) → case locty' of
      (τ₁₁' :→: (η' :* τ₁₂')) → do
        l ← elabEMode $ effectMode η
        l' ← elabEMode $ effectMode η'
        loccondₗ ← (eq_type τ₁₁' τ₁₁)
        loccondᵣ ← (eq_type τ₁₂ τ₁₂')
        return ((eq_mode l l') ⩓ loccondₗ ⩓ loccondᵣ)
    (RefT None τ) → case locty' of
      (RefT None τ') → (eq_type τ τ')
      _  → return False
    (RefT (Some loc) τ) →  case locty' of
      (RefT (Some loc') τ') → do
        l ← elabEMode loc
        l' ← elabEMode loc'
        loccond ← (eq_type τ τ')
        return ((eq_mode l l') ⩓ loccond)
      _  → return False
    (ArrT None _ τ) →  case locty' of
      (ArrT None _ τ') → (eq_type τ τ')
      _  → return False
    (ArrT (Some loc) _ τ) → case locty' of
      (ArrT (Some loc') _ τ') → do
        l ← elabEMode loc
        l' ← elabEMode loc'
        loccond ← (eq_type τ τ')
        return ((eq_mode l l') ⩓ loccond)
      _  → return False
    ISecT loc locty'  → case locty' of
      ISecT loc' locty' → do
        l ← elabEMode loc
        l' ← elabEMode loc'
        loccond ← (eq_type locty locty')
        return ((eq_mode l l') ⩓ loccond)
      _ → return False

-- Possibly add alpha equivalence in the future
eq_type :: STACK ⇒ Type  → Type  → EM 𝔹
eq_type ty ty' = case ty of
  SecT loc loc_ty → case ty' of
      SecT loc' loc_ty' → do
        l ← elabEMode loc
        l' ← elabEMode loc'
        eqcond ← (eq_locty loc_ty loc_ty')
        return ((eq_mode l l') ⩓ eqcond)
      _ → typeError "eq_type: ty' is not a located type" $ frhs
          [ ("ty'", pretty ty' )
          ]
  VarT a → case ty' of
      VarT a' → do
        return (a ≡ a')
      _ → return False
  RecT a τ → case ty' of
      RecT a' τ' → do
        eqcond ← (eq_type τ τ')
        return ((a ≡ a') ⩓ eqcond)
      _ → return False
  ForallT a τ → case ty' of
      ForallT a' τ' → do
        eqcond ← (eq_type τ τ')
        return ((a ≡ a') ⩓ eqcond)
      _ → return False
  _  → typeError "eq_type: ty is not well formed" $ frhs
        [ ("ty", pretty ty )
        ]

-----------------
--- Join functions ---
-----------------
-- Finds meet of two located types (subtype of both)
locty_meet :: STACK ⇒ Type  → Type  → EM Type
locty_meet locty locty' =
  case locty of
  -- sigma = bty
  -- -------Sub-Refl
  -- sigma <: sigma
  BaseT bty → do
    guardErr (locty ≡ locty') $
      typeError "meet: ⊢ₘ _ ˡ→ _ ; locty ≢ locty'" $ frhs
      [ ("locty", pretty locty)
      , ("locty'", pretty locty')
      ]
    return locty
  ShareT p loc locty  → (case locty' of
    ShareT p' loc' locty' →
      do
        l ← (elabEMode loc)
        l' ← (elabEMode loc')
        guardErr ((p  ≡ p') ⩓ (eq_mode l l'))$
          typeError "meet: ⊢ₘ _ ˡ→ _ ; p ≢ p' or l ≢  l'" $ frhs
            [ ("p", pretty p)
            , ("p'", pretty p')
            , ("l", pretty l)
            , ("l'", pretty l')
            ]
      
        loc_meet ← (locty_meet locty locty')
        return (ShareT p loc loc_meet)

    _  → typeError "meet: locty is a share type but locty' is not'" $ frhs
        [ ("locty", pretty locty)
        , ("locty'", pretty locty')
        ]
    )
  -- t1 <: t1' t2 <: t2'
  -- -------Sub-Sum
  -- t1 + t2 <: t1' + t2'
  (tyₗ :+: tyᵣ) → case locty' of
    (ty'ₗ :+: ty'ᵣ) → do

        meet_tyₗ  ← (ty_meet tyₗ ty'ₗ)
        meet_tyᵣ ← (ty_meet tyᵣ ty'ᵣ)
        return (meet_tyₗ :+: meet_tyᵣ)
    _ →  typeError "meet: locty is a sum type but locty' is not'" $ frhs
        [ ("locty", pretty locty)
        , ("locty'", pretty locty')
        ]
  -- t1 <: t1' t2 <: t2'
  -- -------Sub-Pair
  -- t1 x t2 <: t1' x t2'
  (tyₗ :×: tyᵣ) → case locty' of
    (ty'ₗ :×: ty'ᵣ) → do

        meet_tyₗ  ← (ty_meet tyₗ ty'ₗ)
        meet_tyᵣ ← (ty_meet tyᵣ ty'ᵣ)
        return (meet_tyₗ :×: meet_tyᵣ)
    _ →  typeError "meet: locty is a pair type but locty' is not'" $ frhs
        [ ("locty", pretty locty)
        , ("locty'", pretty locty')
        ]

  (ListT n τₜ)  →  case locty' of
    (ListT n' τₜ') → do
      meet_tyₜ ←(ty_meet τₜ τₜ')
      return (ListT n meet_tyₜ)
    _ → typeError "meet: locty is a list type but locty' is not'" $ frhs
        [ ("locty", pretty locty)
        , ("locty'", pretty locty')
        ]
    -- t1' <: t1 t2 <: t2'
  -- -------Sub-Fun
  -- t1 m -> t2 <: t1' m -> t2's
  (τ₁₁ :→: (η :* τ₁₂)) → case locty' of
    (τ₁₁' :→: (η' :* τ₁₂')) → do
        l ← elabEMode $ effectMode η
        l' ← elabEMode $ effectMode η'
        guardErr (eq_mode l l') $
          typeError "meet: l ≢ l'" $ frhs
            [ ("l", pretty l)
            , ("l'", pretty l')
            ]
        join_τ₁₁ ← (locty_join τ₁₁ τ₁₁')
        meet_τ₁₂ ← (locty_meet τ₁₂ τ₁₂')
        return (join_τ₁₁ :→: (η :* meet_τ₁₂))
    -- t <: t' 
  -- -------Sub-RefRO
  -- ref _ t <: ref RO t'
  (RefT None τ)  →  case locty' of
    (RefT None τ') → do
        loc_meet ← (locty_meet τ τ')
        return (RefT None loc_meet)
    (RefT locO τ') → do
        subcond ← (subtype τ' τ  pø)
        guardErr subcond $
          typeError "join: τ' is not a subtype of τ" $ frhs
            [ ("τ", pretty τ)
            , ("τ'", pretty τ')
            ]
        return locty'
    _  → typeError "join: locty' is not a reference type" $ frhs
            [ ("locty'", pretty locty')
            ]
   -- sigma = ref RW#m t
  -- -------Sub-Refl
  -- sigma <: sigma
  (RefT (Some loc) τ)  →  case locty' of
      (RefT None τ') → do
        subcond ← (subtype τ τ'  pø)
        guardErr subcond $
          typeError "join: τ is not a subtype of τ'" $ frhs
            [ ("τ", pretty τ)
            , ("τ'", pretty τ')
            ]
        return locty
      _  → do
        eqcond ← (eq_type locty locty')
        guardErr eqcond $
          typeError "join: one is a read-write reference, locty' is not read only, and locty ≢ locty'" $ frhs
            [ ("locty", pretty locty)
            , ("locty'", pretty locty')
            ] 
        return locty
     -- t <: t' 
  -- -------Sub-RefRO
  -- ref _ t <: ref RO t'
  (ArrT None n τ)  →  case locty' of
    (ArrT None _ τ') → do
        loc_meet ← (locty_join τ τ')
        return (RefT None loc_meet)
    (ArrT locO _ τ') → do
        subcond ← (subtype τ' τ  pø)
        guardErr subcond $
          typeError "join: τ is not a subtype of τ'" $ frhs
            [ ("τ", pretty τ)
            , ("τ'", pretty τ')
            ]
        return locty'
    _  → typeError "join: locty' is not an array type" $ frhs
            [ ("locty'", pretty locty')
            ]
   -- sigma = ref RW#m t
  -- -------Sub-Refl
  -- sigma <: sigma
  (ArrT (Some loc) n τ)  →  case locty' of
    (ArrT None _ τ') → do
        subcond ← (subtype τ' τ  pø)
        guardErr subcond $
          typeError "join: τ is not a subtype of τ'" $ frhs
            [ ("τ", pretty τ)
            , ("τ'", pretty τ')
            ]
        return locty
    _  → do
        eqcond ← (eq_type locty locty')
        guardErr eqcond $
          typeError "join: one is a read-write reference, locty' is not read only, and locty ≢ locty'" $ frhs
            [ ("locty", pretty locty)
            , ("locty'", pretty locty')
            ] 
        return locty
  (ISecT loc loc_ty) →  case locty' of
      (ISecT loc' loc_ty') → do
        loc_union ← (union_em loc loc')
        loc_meet ← (locty_meet loc_ty loc_ty')
        return (ISecT loc_union loc_meet)
      ty' → todoError
  _ → todoError




-- Finds meet of two types
ty_meet :: STACK ⇒ Type  → Type  → EM Type
ty_meet ty ty' = case ty of
  SecT loc loc_ty → case ty' of
      SecT loc' loc_ty' → do
        loc_union ← (union_em loc loc')
        loc_meet ← (locty_meet loc_ty loc_ty')
        return $ SecT loc_union loc_meet
      _ →  typeError "ty_meet: ty is a located type while ty' is not" $ frhs
        [ ("ty", pretty ty )
        , ("ty'", pretty ty' )
        ]
  VarT a → case ty' of
      VarT a' → do
        guardErr (a ≡ a') $
          typeError "ty_meet: ⊢ₘ _ ˡ→ _ ; a ≢ a'" $ frhs
            [ ("a", pretty a)
            , ("a''", pretty a')
            ]
        return ty
      _ → typeError "ty_meet: ty is a type variable while ty' is not" $ frhs
        [ ("ty", pretty ty )
        , ("ty'", pretty ty' )
        ]
  RecT a τ → case ty' of
      RecT a' τ' → do
        subcond ← (subtype ty ty' pø)
        subcond' ← (subtype ty' ty pø)
        if subcond then
          return ty
        else 
          if subcond' then
            return ty'
          else do 
            
            meet ← (ty_meet τ τ')
            guardErr (a ≡ a') $
              typeError "ty_join: ⊢ₘ _ ˡ→ _ ; a ≢ a'" $ frhs
                [ ("a", pretty a)
                , ("a''", pretty a')
                ]
            return $ ForallT a meet
  ForallT a τ → case ty' of
      ForallT a' τ' → do
        subcond ← (subtype ty ty' pø)
        subcond' ← (subtype ty' ty pø)
        if subcond then
          return ty
        else 
          if subcond' then
            return ty'
          else do 
            
            meet ← (ty_meet τ τ')
            guardErr (a ≡ a') $
              typeError "ty_join: ⊢ₘ _ ˡ→ _ ; a ≢ a'" $ frhs
                [ ("a", pretty a)
                , ("a''", pretty a')
                ]
            return $ ForallT a meet
  _  → typeError "ty_meet: ty is not well formed" $ frhs
        [ ("ty", pretty ty )
        ]

-- Finds join of two located types
locty_join :: STACK ⇒ Type  → Type  → EM Type
locty_join locty locty' =
  case locty of
  -- sigma = bty
  -- -------Sub-Refl
  -- sigma <: sigma
  BaseT bty → do
    guardErr (locty ≡ locty') $
      typeError "synApp: ⊢ₘ _ ˡ→ _ ; locty ≢ locty'" $ frhs
      [ ("locty", pretty locty)
      , ("locty'", pretty locty')
      ]
    return locty
  ShareT p loc locty  → case locty' of
    ShareT p' loc' locty' →
      do
        l ← (elabEMode loc)
        l' ← (elabEMode loc')
        guardErr ((p  ≡ p') ⩓ (eq_mode l l'))$
          typeError "join: ⊢ₘ _ ˡ→ _ ; p ≢ p' or l ≢  l'" $ frhs
            [ ("p", pretty p)
            , ("p'", pretty p')
            , ("l", pretty l)
            , ("l'", pretty l')
            ]
      
        loc_join ← (locty_join locty locty')
        return (ShareT p loc loc_join)

    _  → typeError "join: locty is a share type but locty' is not'" $ frhs
        [ ("locty", pretty locty)
        , ("locty'", pretty locty')
        ]
  -- t1 <: t1' t2 <: t2'
  -- -------Sub-Sum
  -- t1 + t2 <: t1' + t2'
  (tyₗ :+: tyᵣ) → case locty' of
    (ty'ₗ :+: ty'ᵣ) → do

        join_tyₗ  ← (ty_join tyₗ ty'ₗ)
        join_tyᵣ ← (ty_join tyᵣ ty'ᵣ)
        return (join_tyₗ :+: join_tyᵣ)
    _ →  typeError "join: locty is a sum type but locty' is not'" $ frhs
      [ ("locty", pretty locty)
      , ("locty'", pretty locty')
      ]
  -- t1 <: t1' t2 <: t2'
  -- -------Sub-Pair
  -- t1 x t2 <: t1' x t2'
  (tyₗ :×: tyᵣ) → case locty' of
    (ty'ₗ :×: ty'ᵣ) → do

        join_tyₗ  ← (ty_join tyₗ ty'ₗ)
        join_tyᵣ ← (ty_join tyᵣ ty'ᵣ)
        return (join_tyₗ :×: join_tyᵣ)

    _ → typeError "join: locty is a pair type but locty' is not'" $ frhs
        [ ("locty", pretty locty)
        , ("locty'", pretty locty')
        ]
  (ListT n τₜ)  →  case locty' of
    (ListT n' τₜ') → do
      join_tyₜ ←(ty_join τₜ τₜ')
      return (ListT n join_tyₜ)
    _ → typeError "join: locty is a list type but locty' is not'" $ frhs
        [ ("locty", pretty locty)
        , ("locty'", pretty locty')
        ]
  -- t1' <: t1 t2 <: t2'
  -- -------Sub-Fun
  -- t1 m -> t2 <: t1' m -> t2'
  (τ₁₁ :→: (η :* τ₁₂)) → case locty' of
    (τ₁₁' :→: (η' :* τ₁₂')) → do
        l ← elabEMode $ effectMode η
        l' ← elabEMode $ effectMode η'
        guardErr (eq_mode l l') $
          typeError "join: l ≢ l'" $ frhs
            [ ("l", pretty l)
            , ("l'", pretty l')
            ]
        meet_τ₁₁ ← (locty_meet τ₁₁ τ₁₁')
        join_τ₁₂ ← (locty_join τ₁₂ τ₁₂')
        return (meet_τ₁₁ :→: (η :* join_τ₁₂))

    -- t <: t' 
  -- -------Sub-RefRO
  -- ref _ t <: ref RO t'
  (RefT None τ)  →  case locty' of
    (RefT None τ') → do
        loc_join ← (locty_join τ τ')
        return (RefT None loc_join)
    (RefT (Some loc) τ') → do
        subcond ← (subtype τ' τ  pø)
        guardErr subcond $
          typeError "join: τ' is not a subtype of τ" $ frhs
            [ ("τ", pretty τ)
            , ("τ'", pretty τ')
            ]
        return locty
    _  → typeError "join: locτy' is not a reference type" $ frhs
            [ ("locty'", pretty locty')
            ]
    -- sigma = ref RW#m t
  -- -------Sub-Refl
  -- sigma <: sigma
  (RefT (Some loc) τ)  →  case locty' of
      (RefT None τ') → do
        subcond ← (subtype τ τ'  pø)
        guardErr subcond $
          typeError "join: τ is not a subtype of τ'" $ frhs
            [ ("τ", pretty τ)
            , ("τ'", pretty τ')
            ]
        return locty
      _  → do
        eqcond ← (eq_locty locty locty' )
        guardErr eqcond $
          typeError "join: one is a read-write reference, locty' is not read/write, and locty ≢ locty'" $ frhs
            [ ("locty", pretty locty)
            , ("locty'", pretty locty')
            ] 
        return locty
  -- sigma = ref RW#m t
  -- -------Sub-Refl
  -- sigma <: sigma
  (ArrT None n τ)  →  case locty' of
    (ArrT None _ τ') → do
        loc_join ← (locty_join τ τ')
        return (ArrT None n loc_join)
    (ArrT locO _ τ') → do
        subcond ← (subtype τ' τ  pø)
        guardErr subcond $
          typeError "join: τ' is not a subtype of τ" $ frhs
            [ ("τ", pretty τ)
            , ("τ'", pretty τ')
            ]
        return locty
    _  → typeError "join: locty' is not an array type" $ frhs
            [ ("locty'", pretty locty')
            ]
   -- t <: t' 
  -- -------Sub-RefRO
  -- ref _ t <: ref RO t'
  (ArrT (Some loc) n τ)  →  case locty' of
    (ArrT None _ τ') → do
        subcond ← (subtype τ τ'  pø)
        guardErr subcond $
          typeError "join: τ is not a subtype of τ'" $ frhs
            [ ("τ", pretty τ)
            , ("τ'", pretty τ')
            ]
        return locty
    _  → do
        eqcond ← (eq_locty locty locty' )
        guardErr eqcond $
          typeError "join: one is a read-write reference. locty' is not read/write, and locty ≢ locty'" $ frhs
            [ ("locty", pretty locty)
            , ("locty'", pretty locty')
            ] 
        return locty
  (ISecT loc loc_ty) → case locty' of
      (ISecT loc' loc_ty') → do
        loc_inter ← (inter_em loc loc')
        loc_top ← (locty_join loc_ty loc_ty')
        return (SecT loc_inter loc_top)
      _ → todoError
  _ → todoError

-- Finds join of two types
-- Finds meet of two types
ty_join :: STACK ⇒ Type  → Type  → EM Type
ty_join ty ty' = case ty of
  SecT loc loc_ty → case ty' of
      SecT loc' loc_ty' → do
        loc_inter ← (inter_em loc loc')
        loc_join ← (locty_join loc_ty loc_ty')
        return $ SecT loc_inter loc_join
      _ →  typeError "ty_join: ty is a located type while ty' is not" $ frhs
        [ ("ty", pretty ty )
        , ("ty'", pretty ty' )
        ]
  VarT a → case ty' of
      VarT a' → do
        guardErr (a ≡ a') $
          typeError "ty_join: ⊢ₘ _ ˡ→ _ ; a ≢ a'" $ frhs
            [ ("a", pretty a)
            , ("a''", pretty a')
            ]
        return ty
      _ → typeError "ty_join: ty is a type variable while ty' is not" $ frhs
        [ ("ty", pretty ty )
        , ("ty'", pretty ty' )
        ]
  RecT a τ → case ty' of
      RecT a' τ' → do
        subcond ← (subtype ty ty' pø)
        subcond' ← (subtype ty' ty pø)
        if subcond then
          return ty
        else 
          if subcond' then
            return ty'
          else do 
            
            join ← (ty_join τ τ')
            guardErr (a ≡ a') $
              typeError "ty_join: ⊢ₘ _ ˡ→ _ ; a ≢ a'" $ frhs
                [ ("a", pretty a)
                , ("a''", pretty a')
                ]
            return $ RecT a join
  ForallT a τ → case ty' of
      ForallT a' τ' → do
        subcond ← (subtype ty ty' pø)
        subcond' ← (subtype ty' ty pø)
        if subcond then
          return ty
        else 
          if subcond' then
            return ty'
          else do 
            
            join ← (ty_join τ τ')
            guardErr (a ≡ a') $
              typeError "ty_join: ⊢ₘ _ ˡ→ _ ; a ≢ a'" $ frhs
                [ ("a", pretty a)
                , ("a''", pretty a')
                ]
            return $ ForallT a join
      _ → typeError "ty_join: ty is a polymorphic type while ty' is not" $ frhs
            [ ("ty", pretty ty )
            , ("ty'", pretty ty' )
            ]
  _  → typeError "ty_join: ty is not well formed" $ frhs
        [ ("ty", pretty ty )
        ]
-- Assumes non empty list of well-formed types
joinList :: STACK ⇒ 𝐿 Type → EM Type
joinList τs =
  case τs of
    Nil → todoError
    τ :& τs → (mfold τ ty_join τs)

-----------------
--- Well formed fnctions functions ---
-----------------

-- Rules to see if any located value is well-formed
wf_loctype :: STACK ⇒ Type → ModeAny →  (𝕏 ⇰ ModeAny) →  EM ()
wf_loctype sigma m bigM =
  case sigma of
     -- WF-Base (Based off WF-INT)
    BaseT bt → return ()
    (ShareT p loc locty) → do
      l ← (elabEMode loc)
      (wf_share_loctype locty m p l)
    (loctyₗ :+: loctyᵣ)  → do
      _ ← (wf_type  loctyₗ m bigM)
      _ ← (wf_type loctyᵣ m bigM)
      return ()
    -- WF-Prod: t1 must be well formed and t2 must be well formed
    (loctyₗ :×: loctyᵣ)  → do
      _ ← (wf_type loctyₗ m bigM)
      _ ← (wf_type loctyᵣ m bigM)
      return ()
    (ListT _ τₜ)  → do
      _ ← (wf_type τₜ m bigM)
      return ()
    -- WF-Fun: m must be same as mode, t1 must be well formed and t2 must be well formed
    (τ₁₁ :→: (η :* τ₁₂)) → do
      m  ← askL terModeL
      l ← elabEMode $ effectMode η
      _ ← (wf_type τ₁₁ m bigM)
      _ ← (wf_type τ₁₂ m bigM)
      guardErr (eq_mode m l) $
        typeError "Not well formed m != l" $ frhs
        [ ("m", pretty m)
        , ("l", pretty l)
        ]
      return ()
    -- WF-Ref: The component type must be well formed 
    (RefT _ τ')  → do
      _ ← (wf_type τ' m bigM)
      return ()
    -- WF-Ref: The component type must be well formed 
    (ArrT _ _ τ')  →  do
      _ ← (wf_type τ' m bigM)
      return ()
    ISecT loc locty → do
 --     _ ← (wf_share_loctype locty m)
      return ()
    _  → typeError "wf_loctype: sigma is not well formed cleartext located type" $ frhs
        [ ("sigma", pretty sigma )
        ]


-- Rules to see if some located value is well-formed
wf_share_loctype :: Type → ModeAny → Prot → ModeAny →  EM ()
wf_share_loctype sigma m p l=
  case sigma of
    BaseT bt → return ()
    (loctyₗ :+: loctyᵣ) → do
      _ ← (wf_share_type loctyₗ m p l)
      _ ← (wf_share_type loctyᵣ m p l) 
      return ()
    (loctyₗ :×: loctyᵣ) → do
      _ ← (wf_share_type loctyₗ m p l)
      _ ← (wf_share_type loctyᵣ m p l) 
      return ()
    (ListT _ τₜ)  → do
      _ ← (wf_share_type τₜ m p l)
      return ()
    _  → do
      typeError "wf_share_loctype: sigma is not well formed encrypted type" $ frhs
        [ ("sigma", pretty sigma)
        ]

wf_share_type :: Type → ModeAny →  Prot → ModeAny → EM ()
wf_share_type ty m p l=
  case ty of
    -- WF-Loc
    SecT em' (ShareT p' loc loc_ty) → do
      m' ← (elabEMode em')
      guardErr (supermode m m') $
        typeError "wf_share_type: m is not a superset of m'" $ frhs
        [ ("m", pretty m)
        , ("m'", pretty m')
        ]
      l' ← (elabEMode loc)
      guardErr (eq_mode l l') $
        typeError "wf_share_type: Not well formed encrypted type l != l'" $ frhs
        [ ("l", pretty l)
        , ("l'", pretty l')
        ]
      guardErr (eq_mode m m') $
        typeError "wf_share_type: Not well formed encrypted type m != m'" $ frhs
        [ ("m", pretty m)
        , ("m'", pretty m')
        ]
      wfcond ← (wf_share_loctype loc_ty m' p l)
      return ()
    _ → typeError "wf_share_type: ty is not well formed" $ frhs
        [ ("ty", pretty ty )
        ]



-- Rules to see if the type is well formed in terms of a good AST (Share rules)
wf_type :: Type → ModeAny → (𝕏 ⇰ ModeAny)→ EM ()
wf_type ty m bigM =
  case ty of

    -- WF-Loc
    SecT em' locty → do
      m' ← (elabEMode em')
      guardErr (supermode m m') $
        typeError "wf_type: m is not a superet of m'" $ frhs
        [ ("m", pretty m)
        , ("m'", pretty m')
        ]
      wfcond ← (wf_loctype locty m' bigM)
      return ()
    -- WF-Var
    VarT a → do
      case bigM ⋕? a of
        Some m' → do
          guardErr (supermode m m') $
            typeError "wf_type: m is not a superet of m'" $ frhs
              [ ("m", pretty m)
              , ("m'", pretty m')
              ]
        None → typeError "wf_type: M does not contain a" $ frhs
          [ ("M", pretty bigM)
          , ("a", pretty a)
          ]
    -- WF-Rec
    RecT a τ → do
      m'  ← (get_intersect_type a τ m m)
      guardErr (supermode m m') $
        typeError "wf_type: m is not a superset of m'" $ frhs
          [ ("m", pretty m)
          , ("m'", pretty m')
          ]
      (wf_type τ m' ((a ↦ m') ⩌ bigM))
    -- WF-Poly
    ForallT a τ → do
      m'  ← (get_intersect_type a τ m m)
      guardErr (supermode m m') $
        typeError "wf_type: m is not a superet of m'" $ frhs
          [ ("m", pretty m)
          , ("m'", pretty m')
          ]
      (wf_type τ m' ((a ↦ m') ⩌ bigM))
    _ → typeError "wf_type: ty is not well formed" $ frhs
        [ ("ty", pretty ty )
        ]

get_intersect_loc_type :: STACK ⇒ TVar →Type → ModeAny → ModeAny → EM ModeAny
get_intersect_loc_type x sigma m m' =
  case sigma of
     -- WF-Base (Based off WF-INT)
    BaseT bt → return m
    (ShareT _ _ τ) → (get_intersect_loc_type x τ m m')
    (loctyₗ :+: loctyᵣ)  → do
      mₗ  ← (get_intersect_type x loctyₗ m m')
      mᵣ  ← (get_intersect_type x loctyᵣ m m')
      return (inter_m  mₗ mᵣ )
    -- WF-Prod: t1 must be well formed and t2 must be well formed
    (loctyₗ :×: loctyᵣ)  → do
      mₗ  ← (get_intersect_type x loctyₗ m m')
      mᵣ  ← (get_intersect_type x loctyᵣ m m')
      return (inter_m  mₗ mᵣ )
    (ListT _ τₜ)  → 
      (get_intersect_type x τₜ m m')
    -- WF-Fun: m must be same as mode, t1 must be well formed and t2 must be well formed
    (τ₁₁ :→: (η :* τ₁₂)) → do
      m₁₁  ← (get_intersect_type x τ₁₁ m m')
      m₁₂  ← (get_intersect_type x τ₁₂ m m')
      return (inter_m  m₁₁ m₁₂)
    -- WF-Ref: The component type must be well formed 
    (RefT _ τ')  → 
      (get_intersect_type x τ' m m')
    -- WF-Ref: The component type must be well formed 
    (ArrT _ _ τ')  →  
      (get_intersect_type x τ' m m')
    ISecT loc locty → 
      (get_intersect_type x locty m m')
    _  → typeError "get_intersect_loctype: sigma is not well formed located type" $ frhs
        [ ("sigma", pretty sigma )
        ]

-- Rules to see if the type is well formed in terms of a good AST (Share rules)
get_intersect_type :: TVar  → Type → ModeAny → ModeAny  → EM ModeAny
get_intersect_type x τ m m' =
   case  τ of 
    SecT em'' sigma →  do
      m''  ← elabEMode em''
      (get_intersect_loc_type x sigma m m'')
    VarT a → do
      return (if (x ≡ a) then m' else m)
    -- WF-Rec
    RecT a τ → do
      if (x ≡ a) then (return m) else (get_intersect_type x τ m m')
    -- WF-Poly
    ForallT a τ → do
      if (x ≡ a) then (return m) else (get_intersect_type x τ m m')
    _  → typeError "get_intersect_type: τ is not well formed type" $ frhs
      [ ("τ", pretty τ  )
      ]
-- Rules to get the least sub subtype of loctype sigma that is well formed for some M
sublocty_wf :: STACK ⇒ Type  → ModeAny →  (𝕏 ⇰ ModeAny)  → EM Type
sublocty_wf sigma m bigM=
  case sigma of
    -- WF-Base (Based off WF-INT)
    BaseT bt → return sigma
    ShareT p loc loc_ty  → do
      loc_subty ← (sublocty_wf loc_ty m bigM)
      return (ShareT p loc loc_subty)
    -- WF-Sum: t1 must be well formed and t2 must be well formed
    (loctyₗ :+: loctyᵣ) → do
      loctyₗ' ← (subty_wf loctyₗ m bigM)
      loctyᵣ' ← (subty_wf loctyᵣ m bigM)
      return (loctyₗ' :+: loctyᵣ')
    (loctyₗ :×: loctyᵣ)  → do
      loctyₗ' ← (subty_wf loctyₗ m bigM)
      loctyᵣ' ← (subty_wf loctyᵣ m bigM)
      return (loctyₗ' :×: loctyᵣ')
    (ListT n τₜ)  → do
      τₜ' ← (subty_wf τₜ m bigM)
      return (ListT n τₜ')
    -- WF-Fun: m must be same as mode, t1 must be well formed and t2 must be well formed
    (τ₁₁ :→: (η :* τ₁₂)) → do
      l ← elabEMode $ effectMode η
      guardErr (eq_mode m l) $
        typeError "subloctype_wf: Not well formed m != l" $ frhs
        [ ("m", pretty m)
        , ("l", pretty l)
        ]
      τ₁₁' ← (superty_wf τ₁₁ m bigM)
      τ₁₂' ← (subty_wf τ₁₂ m bigM)
      return (τ₁₁' :→:  (η :* τ₁₂'))
    -- WF-Ref: The component type must be well formed 
    (RefT loc τ)  → do
      τ' ← (subty_wf τ m bigM)
      return (RefT loc τ')
    -- WF-Ref: The component type must be well formed 
    (ArrT loc n τ)  → do
      τ' ← (subty_wf τ m bigM)
      return (ArrT loc n τ')
    (ISecT loc loc_ty) → do
      loc_subty ← (sublocty_wf loc_ty m bigM)
      (return (ISecT loc loc_subty))
    _  → typeError "subloctype_wf: sigma is not well structured" $ frhs
        [ ("sigma", pretty sigma )
        ]



-- Rules to get the least super supertype of type t that is well formed for some M
subty_wf :: STACK ⇒ Type  → ModeAny  → (𝕏 ⇰ ModeAny) → EM Type
subty_wf t m bigM =
    case t of
    SecT loc loc_ty → do
      m' ← (elabEMode loc)
      loc_subty ← (superlocty_wf loc_ty m' bigM)
      guardErr (supermode m m') $
        typeError "subtype_wf: m is not a superset of m'" $ frhs
        [ ("m", pretty m)
        , ("m'", pretty m')
        ]
      (return (SecT loc loc_subty))
      -- WF-Var
    VarT a → do
      case bigM ⋕? a of
        Some m' → do
          guardErr (supermode m m') $
            typeError "subtype_wf: m is not a superet of m" $ frhs
              [ ("m", pretty m)
              , ("m'", pretty m')
              ]
          return t
        None → typeError "subtype_wf: M does not contain a"$ frhs
          [ ("M", pretty bigM)
          , ("a", pretty a)
          ]
    -- WF-Rec
    RecT a τ → do
      m'  ← (get_intersect_type a τ m m)
      guardErr (supermode m m') $
        typeError "subtype_wf: m is not a superset of m'" $ frhs
          [ ("m", pretty m)
          , ("m'", pretty m')
          ]
      subty ← (subty_wf τ m' ((a ↦ m') ⩌ bigM))
      return (RecT a subty )
    -- WF-Poly
    ForallT a τ → do
      m'  ← (get_intersect_type a τ m m)
      guardErr (supermode m m') $
        typeError "subtype_wf: m is not a superset of m'" $ frhs
          [ ("m", pretty m)
          , ("m'", pretty m')
          ]
      subty ← (subty_wf τ m' ((a ↦ m') ⩌ bigM))
      return (ForallT a subty )
    _  → typeError "subtype_wf: t is not well structured" $ frhs
        [ ("t", pretty t )
        ]


-- Rules to get the least super supertype of loctype sigma that is well formed
superlocty_wf :: STACK ⇒ Type  → ModeAny → (𝕏 ⇰ ModeAny) → EM Type
superlocty_wf sigma m bigM =
  case sigma of
    -- WF-Base (Based off WF-INT)
    BaseT bt → return sigma
    ShareT p loc loc_ty  → do
        loc_superty ← (superlocty_wf loc_ty m bigM)
        return (ShareT p loc loc_superty)
    -- WF-Sum: t1 must be well formed and t2 must be well formed
    (loctyₗ :+: loctyᵣ) → do
      loctyₗ' ← (superty_wf loctyₗ m bigM)
      loctyᵣ' ← (superty_wf loctyᵣ m bigM)
      return (loctyₗ' :+: loctyᵣ')
    (loctyₗ :×: loctyᵣ)  → do
      loctyₗ' ← (superty_wf loctyₗ m bigM)
      loctyᵣ' ← (superty_wf loctyᵣ m bigM)
      return (loctyₗ' :×: loctyᵣ')
    (ListT n τₜ)  → do
      τₜ' ← (superty_wf τₜ m bigM)
      return (ListT n τₜ')
    -- WF-Fun: t1 must be well formed and t2 must be well formed
    (τ₁₁ :→: (η :* τ₁₂)) → do
      l ← elabEMode $ effectMode η
      guardErr (eq_mode m l) $
        typeError "superloctype_wf: Not well formed m != l" $ frhs
        [ ("m", pretty m)
        , ("l", pretty l)
        ]
      τ₁₁' ← (subty_wf τ₁₁ m bigM)
      τ₁₂' ← (superty_wf τ₁₂ m bigM)
      return (τ₁₁' :→:  (η :* τ₁₂'))
    -- WF-Ref: The component type must be well formed 
    (RefT loc τ)  → do
      τ' ← (superty_wf τ m bigM)
      return (RefT loc τ')
    -- WF-Ref: The component type must be well formed 
    (ArrT loc n τ)  → do
      τ' ← (superty_wf τ m bigM)
      return (ArrT loc n τ')
    (ISecT loc loc_ty) → do
      loc_subty ← (superlocty_wf loc_ty m bigM)
      (return (ISecT loc loc_subty))
    _  → typeError "superloctype_wf: sigma is not well structured" $ frhs
        [ ("sigma", pretty sigma )
        ]



-- Rules to get the least super supertype of type t that is well formed
superty_wf :: STACK ⇒ Type  → ModeAny  → (𝕏 ⇰ ModeAny) →  EM Type
superty_wf t m bigM=
    case t of
    SecT loc loc_ty → do
        l ← (elabEMode loc)
        l_inter ← (elabMode (inter_m m l))
        loc_superty ← (superlocty_wf loc_ty m bigM)
        return (SecT l_inter loc_superty)
          -- WF-Var
    VarT a → do
      case bigM ⋕? a of
        Some m' → do
          guardErr (supermode m m') $
            typeError "supertype_wf: m is not a superet of m'" $ frhs
              [ ("m", pretty m)
              , ("m'", pretty m')
              ]
          return t
        None → typeError "supertype_wf: M does not contain a" $ frhs
          [ ("M", pretty bigM)
          , ("a", pretty a)
          ]
    -- WF-Rec
    RecT a τ → do
      m'  ← (get_intersect_type a τ m m)
      guardErr (supermode m m') $
        typeError "supertype_wf: m is not a superset of m'" $ frhs
          [ ("m", pretty m)
          , ("m'", pretty m')
          ]
      superty ← (superty_wf τ m' ((a ↦ m') ⩌ bigM))
      return (RecT a superty )
    -- WF-Poly
    ForallT a τ → do
      m'  ← (get_intersect_type a τ m m)
      guardErr (supermode m m') $
        typeError "supertype_wf: m is not a superset of m'" $ frhs
          [ ("m", pretty m)
          , ("m'", pretty m')

          ]
      superty ← (superty_wf τ m' ((a ↦ m') ⩌ bigM))
      return (ForallT a superty )
    _  → typeError "supertype_wf: t is not well structured" $ frhs
        [ ("t", pretty t )
        ]


loc_type_subst ::  STACK ⇒ Var   → Type → Type → EM Type
loc_type_subst x sigma ty =
  case sigma of
    -- WF-Base (Based off WF-INT)
    BaseT bt → return sigma
    ShareT p loc loc_ty  → (type_subst x loc_ty ty)
    -- WF-Sum: t1 must be well formed and t2 must be well formed
    (loctyₗ :+: loctyᵣ) → do
      loctyₗ' ← (type_subst x loctyₗ ty)
      loctyᵣ' ← (type_subst x loctyᵣ ty)
      return (loctyₗ' :+: loctyᵣ')
    (loctyₗ :×: loctyᵣ)  → do
      loctyₗ' ← (type_subst x loctyₗ ty)
      loctyᵣ' ← (type_subst x loctyᵣ ty)
      return (loctyₗ' :×: loctyᵣ')
    (ListT n τₜ)  → do
      τₜ' ←  (type_subst x τₜ ty)
      return (ListT n τₜ')
    -- WF-Fun: m must be same as mode, t1 must be well formed and t2 must be well formed
    (τ₁₁ :→: (η :* τ₁₂)) → do
      τ₁₁' ←  (type_subst x τ₁₁ ty)
      τ₁₂' ← (type_subst x τ₁₂ ty)
      return (τ₁₁' :→:  (η :* τ₁₂'))
    -- WF-Ref: The component type must be well formed 
    (RefT loc τ)  → do
      τ' ← (type_subst x τ ty)
      return (RefT loc τ')
    -- WF-Ref: The component type must be well formed 
    (ArrT loc n τ)  → do
      τ' ← (type_subst x τ ty)
      return (ArrT loc n τ')
    (ISecT loc loc_ty) → do
      loc_ty' ← (type_subst x loc_ty ty)
      (return (ISecT loc loc_ty'))
    _  → typeError "loc_type_subst: sigma is not well structured" $ frhs
        [ ("sigma", pretty sigma )
        ]

type_subst ::  STACK ⇒ Var   → Type → Type → EM Type
type_subst x ty ty' =
  case ty of
    -- WF-Loc
    SecT em locty → do
      locty' ← (loc_type_subst x locty ty')
      return (SecT em locty')
    VarT x'  → return (if x ≡ x' then ty' else ty) 
    RecT x' ty'' → if x ≡ x' then (return ty) else (loc_type_subst x ty'' ty') 
    ForallT x' ty'' → if x ≡ x' then (return ty) else (loc_type_subst x ty'' ty') 
    _ → typeError "type_subst: ty is not well structured" $ frhs
        [ ("ty", pretty ty )
        ]
-----------------
--- Bind Typing ---
-----------------

-- Maps a type to a variable in the context
bindTo ∷ STACK ⇒ Var → Type → EM a → EM a
bindTo x τ = mapEnvL terEnvL ((x ↦ τ) ⩌)

-- Returns a function that will change the environment based on the pattern
bindType ∷ STACK ⇒ Type → Pat → (EM (EM a → EM a))
bindType τ ψ = matchType τ ψ

-- assume type is well formed to the current m
matchType ∷ STACK ⇒  Type → Pat → EM (EM a → EM a)
matchType τ ψ= case ψ of
  VarP x → return (bindTo  x τ)
  BulP → case τ of
    (SecT loc (BaseT (UnitT) )) →  do
          m ← askL terModeL
          l ← elabEMode loc
          guardErr (eq_mode m l) $
            typeError "matchType: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
              , ("l", pretty l)
              ]
          return id
    (SecT loc (ShareT _ _ (BaseT (UnitT) ))) →  do
          m ← askL terModeL
          l ← elabEMode loc
          guardErr (eq_mode m l) $
            typeError "matchType: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
              , ("l", pretty l)
              ]
          return id
    _ → typeError "matchType: ⊢ₘ _ ˡ→ _ ; () is not of type τ" $ frhs
              [ ("τ", pretty τ)
              ]
  EPrinSetP  → case τ of
    (SecT loc (BaseT ℙsT)) → do
          m ← askL terModeL
          l ← elabEMode loc
          guardErr (eq_mode m l) $
            typeError "matchType: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
              , ("l", pretty l)
              ]
          return id
    _ → typeError "matchType: ⊢ₘ _ ˡ→ _ ; {} is not of type τ" $ frhs
              [ ("τ", pretty τ)
              ]
  NEPrinSetP x ψ   → case τ of
    (SecT loc (BaseT ℙsT ))  →  do
          m ← askL terModeL
          l ← elabEMode loc
          guardErr (eq_mode m l) $
            typeError "matchType: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
              , ("l", pretty l)
              ]
          return (\y -> (
            do
            mt ← (bindType  (SecT loc (BaseT ℙsT )) ψ)
            (mt  ((bindTo  x (SecT loc (BaseT ℙT ))) y)) ))
    _ → typeError "matchType: ⊢ₘ _ ˡ→ _ ; the expression is not of type SecT loc τ" $ frhs
              [ ("τ", pretty (BaseT ℙsT ))
              ]
  ProdP ψₗ ψᵣ  →     case τ of
    (SecT loc (τₗ :×: τᵣ)) → do
        m ← askL terModeL
        l ← elabEMode loc
        guardErr (eq_mode m l) $
          typeError "matchType: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
              , ("l", pretty l)
              ]
        return (\x -> (
          do
          ml ←  (bindType τₗ ψₗ)
          mr ←  (bindType τᵣ ψᵣ)
          (mr (ml x)) ))
    _ → todoError
  LP ψₗ → case τ of
    (SecT loc (τₗ  :+: _)) → do
        m ← askL terModeL
        l ← elabEMode loc
        guardErr (eq_mode m l) $
          typeError "matchType: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
              , ("l", pretty l)
              ]
        (bindType τₗ ψₗ)
    (SecT loc (ShareT _ _ (τₗ  :+: _))) → do
        m ← askL terModeL
        l ← elabEMode loc
        guardErr (eq_mode m l) $
          typeError "matchType: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
              , ("l", pretty l)
              ]
        (bindType τₗ ψₗ)
    _ → typeError "matchType: ⊢ₘ _ ˡ→ _ ; type τ is not a sumtype" $ frhs
              [ ("τ", pretty τ)
              ]
  RP ψᵣ → case τ of
    (SecT loc (τₗ  :+: τᵣ)) → do
        m ← askL terModeL
        l ← elabEMode loc
        guardErr (eq_mode m l) $
          typeError "matchType: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
          [ ("m", pretty m)
              , ("l", pretty l)
          ]
        (bindType τᵣ ψᵣ)
    (SecT loc (ShareT _ _ (τₗ  :+: τᵣ))) → do
        m ← askL terModeL
        l ← elabEMode loc
        guardErr (eq_mode m l) $
          typeError "matchType: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
              , ("l", pretty l)
              ]
        (bindType τᵣ ψᵣ)
    _ → typeError "matchType: ⊢ₘ _ ˡ→ _ ; type τ is not a sumtype" $ frhs
              [ ("τ", pretty τ)
              ]
  NilP → case τ of
    (SecT loc (ListT _ τₜ)) → do
          m ← askL terModeL
          l ← elabEMode loc
          guardErr (eq_mode m l) $
            typeError "matchType: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
              , ("l", pretty l)
              ]
          return id
    _ → typeError "matchType: ⊢ₘ _ ˡ→ _ ; '() is not of type τ" $ frhs
              [ ("τ", pretty τ)
              ]
  ConsP ψ ψₜ → case τ of
    (SecT loc (ListT n τₜ)) → do
          m ← askL terModeL
          l ← elabEMode loc
          guardErr (eq_mode m l) $
            typeError "matchType: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
              , ("l", pretty l)
              ]
          return (\x -> (
            do
              mh ←  (bindType τₜ ψ)
              mt ←  (bindType τ ψₜ)
              mt $ mh $ x))
    _ → typeError "matchType: ⊢ₘ _ ˡ→ _ ; the type τ is not of type (SecT loc (ListT n τₜ))" $ frhs
              [ ("τ", pretty τ)
              ]
  EBundleP   → case τ of
     (SecT loc₁ (ISecT loc₁' τ₁'))  → do
        m  ← askL terModeL
        l₁ ← elabEMode loc₁
        --  dont need subcond  ←  (subtype τ (SecT m (RefT t')))
        guardErr (eq_mode m l₁) $
            typeError "matchType: ⊢ₘ _ ˡ→ _ ; m ≢ l₁" $ frhs
              [ ("m", pretty m)
              , ("l", pretty l)
              ]
          return id
    _ → typeError "matchType: ⊢ₘ _ ˡ→ _ ; The empty bundle is not of type τ" $ frhs
              [ ("τ", pretty τ)
              ]
  NEPrinSetP x ψ ψₜ   → case τ of
    (SecT loc₁ (ISecT loc₁' τ₁'))  → do
        m  ← askL terModeL
        l₁ ← elabEMode loc₁
        --  dont need subcond  ←  (subtype τ (SecT m (RefT t')))
        guardErr (eq_mode m l₁) $
            typeError "matchType: ⊢ₘ _ ˡ→ _ ; m ≢ l₁" $ frhs
              [ ("m", pretty m)
              , ("l", pretty l)
              ]
          return (\y -> (
            do
            mh ← (bindType τ₁' ψ)
            mt ← (bindType τ ψₜ )
            (mh (mt  ((bindTo  x (SecT loc (BaseT ℙT ))) y)) )))
    _ → typeError "matchType: ⊢ₘ _ ˡ→ _ ; the expression is not of type SecT loc τ" $ frhs
              [ ("τ", pretty (BaseT ℙsT ))
              ]
     
    AscrP ψ τ'
      subcond  ← (subtype τ τ' pø) 
      guardErr subcond $
        typeError "matchType: e has type τ' which is not a subtype of τ" $ frhs
        [ ("e", pretty e)
        , ("τ", pretty τ)
        , ("τ'", pretty τ')
        ]
      return id
  WildP → return id


------------------------------------------------
-- Static Evaluation of Principal Expressions --
------------------------------------------------
setToList :: STACK ⇒ (𝑃 a)  → (𝐿 a)
setToList myset = list𝐼 (iter myset)

listToSet :: STACK ⇒ (Ord a) ⇒ (𝐿 a)  → (𝑃 a)
listToSet mylist = pow𝐼 (iter mylist)

inPrins ∷ STACK ⇒ (𝑃 𝕏) → PrinExp →  𝔹
inPrins prins  ρe = case  ρe of
  VarPE x       → x ∈ prins
  -- get rid of
  AccessPE x n₁ → False



elabPrinExp ∷ STACK ⇒ PrinExp → EM PrinVal
elabPrinExp ρe = case  ρe of
  VarPE x       → return (SinglePV (𝕩name x))
  -- get rid of
  AccessPE x n₁ → todoError

elabPrinSetExp ∷ STACK ⇒ PrinSetExp → EM ((𝑃 PrinVal) ∨ ())
elabPrinSetExp ρse = case  ρse of
  PowPSE ρel → do
    prins ← askL terPrinsL
    if (and (map (inPrins prins) ρel)) then do
      pvl ← (mapM elabPrinExp ρel )
      (let ρvs = (listToSet pvl) in (return (Inl ρvs)))
    else
      return (Inr ())
  VarPSE _  → return (Inr ())
  AnyPSE → return (Inr ())
  _ → todoError


elabEMode ∷ STACK ⇒ EMode → EM ModeAny
elabEMode l =  do
  em ← ((mapM elabPrinSetExp) l) 
  case em of
    Top → return (AddAny Top)
    AddTop  (Inl ρvs) → return (AddAny (AddTop ρvs))
    _  → return Any


elabPrinVal :: STACK ⇒ PrinVal → EM PrinExp
elabPrinVal ρv = case  ρv of
  (SinglePV ρ)    → return (VarPE (var ρ))
  (AccessPV ρ n₁) → return (AccessPE (var ρ) n₁)



-- turn powerset to list, map the list, convert to prinsetexp
elabPrinValSet :: STACK ⇒ (𝑃 PrinVal)  → EM PrinSetExp
elabPrinValSet ρvs =
    let ρvl = (setToList ρvs) in do
    ρel ← (mapM elabPrinVal ρvl)
    (return (PowPSE ρel))

elabMode ∷ STACK ⇒ ModeAny → EM EMode
elabMode m = case m of
  (Any) → return (AddTop AnyPSE) 
  (AddAny  ρvs) → (mapM elabPrinValSet ρvs)
