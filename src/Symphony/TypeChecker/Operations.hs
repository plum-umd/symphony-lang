module Symphony.TypeChecker.Operations where

import UVMHS
import AddToUVMHS

import Symphony.Syntax
import Symphony.TypeChecker.Error
import Symphony.TypeChecker.TLM hiding (TLR)
import Symphony.TypeChecker.EM


-----------------
--- Primitives ---
-----------------

-- Takes an op, list of base types, and returns what the op should return on the base type 
primType ∷ Op → 𝐿 BaseType → EM BaseType
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
extractProt :: Type → EM (𝑂 (Prot, Mode) )
extractProt τ =
 case τ of 
  (SecT _  (ShareT p loc _))   → do
    l ← elabEMode loc
    return (Some (p, l))
  (SecT _ _)  → return None
  _ → todoError

assertM :: Mode → Type → EM ()
assertM m τ =
  case τ of 
    (SecT loc _)  →  do
          l ← elabEMode loc
          if (m == l) then return () else todoError 
    _  → todoError

-- Extracts basetype
extractBase :: Type → EM BaseType
extractBase τ =
   case τ of 
     (SecT _ (BaseT bτ))  → return bτ
     (SecT _ (ShareT _ _ (BaseT bτ)))  →  return bτ
     _ → todoError

embedShare ::  Prot → EMode → Type → EM Type
embedShare φ l τ = 
  case τ of 
    (SecT l' (ShareT φ' l'' (BaseT bτ))) → do
      q ← elabEMode l
      q'' ← elabEMode l''
      guardErr ((q ≡ q'') ⩓ φ ≡ φ) $
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

assertShareable ::   Type → EM ()
assertShareable τ = 
  case τ of 
    (SecT l' (BaseT bτ))  → return ()
    (SecT l' (τₗ :+: τᵣ) )  → do
      _ ← (assertShareable τₗ )
      _ ← (assertShareable τᵣ )
      return ()
    _ → todoError

eModeEqual :: EMode → EMode → EM 𝔹
eModeEqual loc loc' = 
  do
    p ←  elabEMode loc
    p' ← elabEMode loc'
    return $ p ≡ p'

{-
-- gets a type stripped of locations and a well formed type
assertShareableType :: Type → Type → Prot → EMode → EM ()
assertShareableType τ₁ τ₂ q φ =
  case τ₁ of 
    (BaseT bτ₁) → 
      case τ₂ of 
        (SecT l' (BaseT bτ₂))  → if (bτ₁ == bτ₂) 
          then
            return ()
          else
            typeError "bτ₁ != bτ₂" $ frhs
              [ ("bτ₁", pretty bτ₁)
              , ("bτ₂", pretty bτ₂)
              ]
        (SecT l' (ShareT φ' l'' (BaseT bτ₂))) → if (bτ₁ == bτ₂) 
          then do
            emodeCond ← eModeEqual q l''
            if (emodeCond &&  φ == φ' ) 
            then
              return ()
            else
              typeError "The protocols are not equal" $ frhs
                [ ("q", pretty q)
                , ("l''", pretty l'')
                , ("φ", pretty  φ)
                , ("φ'", pretty  φ')
                ] 
          else
            typeError "bτ₁ != bτ₂" $ frhs
              [ ("bτ₁", pretty bτ₁)
              , ("bτ₂", pretty bτ₂)
              ]
     (τₗ₁ :+: τᵣ₁)  → case τ₂ of 
        (SecT l' (τₗ₂ :+: τᵣ₂) ) →  do
          _ ← (assertShareableType τₗ₁ τₗ₂)
          _ ← (assertShareableType τᵣ₁ τᵣ₂)
          return ()
        (SecT l' (ShareT φ' l''  (τₗ₂ :+: τᵣ₂)) ) →  do
          _ ← (assertShareableType τₗ₁ τₗ₂)
          _ ← (assertShareableType τᵣ₁ τᵣ₂)
          emodeCond ← eModeEqual q l''
        if (emodeCond &&  φ == φ' ) 
          then
            return ()
          else
            typeError "The protocols are not equal" $ frhs
              [ ("q", pretty q)
                , ("l''", pretty l'')
                , ("φ", pretty  φ)
                , ("φ'", pretty  φ')
              ] 
    _ → todoError
    -}
-----------------
--- Subtype utility ---
-----------------

-- Check if loctyS <: loctyT
subtype_loc :: Type → Type → EM 𝔹
subtype_loc loctyS loctyT = case loctyS of
  -- sigma = bty 
  -- -------Sub-Refl
  -- sigma <: sigma 
  BaseT bty → return (loctyS ≡ loctyT)
  ShareT pS loc loctyS  → case loctyT of
      ShareT pT loc' loctyT → do 
        l ← (elabEMode loc)
        l' ← (elabEMode loc')
        loccond ← (subtype_loc loctyS loctyT)
        return ((l == l') ⩓ (pS == pT) ⩓ loccond)
      _  → return False
  -- t1 <: t1' t2 <: t2'
  -- -------Sub-Sum
  -- t1 + t2 <: t1' + t2' 
  (loctySₗ :+: loctySᵣ) → case loctyT of
    (loctyTₗ :+: loctyTᵣ) → do 

        loccondₗ ← (subtype_loc loctySₗ loctyTₗ)
        loccondᵣ ← (subtype_loc loctySᵣ loctyTᵣ)
        return (loccondₗ ⩓ loccondᵣ)
    _ → return False 
  -- t1 <: t1' t2 <: t2'
  -- -------Sub-Pair
  -- t1 x t2 <: t1' x t2' 
  (loctySₗ :×: loctySᵣ) → case loctyT of
    (loctyTₗ :×: loctyTᵣ) → do 
        loccondₗ ← (subtype_loc loctySₗ loctyTₗ)
        loccondᵣ ← (subtype_loc loctySᵣ loctyTᵣ)
        return (loccondₗ ⩓ loccondᵣ)
    _ → return False
  (ListT _ τₜ)  →  case loctyT of
    (ListT _ τₜ') → (subtype_loc τₜ τₜ')
    _ → return False
  -- t1' <: t1 t2 <: t2'
  -- -------Sub-Fun
  -- t1 m -> t2 <: t1' m -> t2' 
  (τ₁₁ :→: (η :* τ₁₂)) → case loctyT of
    (τ₁₁' :→: (η' :* τ₁₂')) → do 
        l ← elabEMode $ effectMode η
        l' ← elabEMode $ effectMode η'
        loccondₗ ← (subtype_loc τ₁₁' τ₁₁)
        loccondᵣ ← (subtype_loc τ₁₂ τ₁₂')
        return ((l ≡ l') ⩓ loccondₗ ⩓ loccondᵣ)
  (RefT None τ) →  case loctyT of
    (RefT None τ') → (subtype_loc τ τ')
    _  → return False
  (RefT _ τ) → case loctyT of
    (RefT None τ') → (subtype_loc τ τ')
    _  → return (loctyS == loctyT)
  (ArrT None _ τ) →  case loctyT of
    (ArrT None _ τ') → (subtype_loc τ τ')
    _  → return False
  (ArrT _ _ τ) → case loctyT of
    (ArrT None _ τ') → (subtype_loc τ τ')
    _  → return (loctyS == loctyT)
  ISecT locS loctyS  → case loctyT of
      ISecT locT loctyT → do 
        mcond ← (superemode locS locT)
        loccond ← (subtype_loc loctyS loctyT)
        return (mcond ⩓ loccond)
  _ → return False

-- Check if tyS <: tyT
subtype :: Type → Type → EM 𝔹
  -- sigma <: sigma' m ⊇ m'
  -- -------Sub-Loc
  -- sigma@m <: sigma'@m' 
subtype tyS tyT = case tyS of
  SecT locS loctyS → case tyT of
      SecT locT loctyT → do 
        mcond ← (superemode locS locT)
        loccond ← (subtype_loc loctyS loctyT)
        return (mcond ⩓ loccond)
      _ → return False
  _ → return False


-- Check if tyT >: tyS
supertype :: Type → Type → EM 𝔹
supertype tyT tyS = subtype tyS tyT

-- Checks if emT ⊇ emS
superemode :: EMode → EMode → EM 𝔹
superemode locT locS= do
  lT ← elabEMode locT
  lS ← elabEMode locS
  return (supermode lT lS)

-- Checks if mT ⊇ mS
supermode :: Mode → Mode → 𝔹
supermode locT locS = case locT of
  Top → True
  AddTop psT → case locS of
      Top → False
      AddTop psS  → (psT ⊇ psS)

 -- Returns em ∩ em'
inter_em :: EMode → EMode → EM EMode
inter_em loc loc' = do
  l ← elabEMode loc
  l' ← elabEMode loc'
  (elabMode (l ⊓ l'))
 
-- Returns m ∩ m'
inter_m :: Mode → Mode → Mode
inter_m l l' = case l of
  Top → l'
  AddTop ps → case l' of
      Top → (AddTop ps)
      AddTop ps'  →  AddTop(ps ∩ ps')

 -- Returns em ∩ em'
union_em :: EMode → EMode → EM EMode
union_em loc loc' = do
  l ← elabEMode loc
  l' ← elabEMode loc'
  (elabMode (l ⊔ l'))
 
-- Returns m ∩ m'
union_m :: Mode → Mode → Mode
union_m l l' = case l of
  Top → Top
  AddTop ps → case l' of
      Top → Top
      AddTop ps'  →  AddTop(ps ∪ ps')

-----------------
--- Join functions ---
-----------------
-- Finds meet of two located types (subtype of both)
locty_meet :: Type  → Type  → EM Type 
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
        if ((p == p') ⩓ (l == l'))
          then (
            do
              loc_meet ← (locty_meet locty locty')
              return (ShareT p loc loc_meet)
          )
        else todoError
      
    _  → todoError
    )
  -- t1 <: t1' t2 <: t2'
  -- -------Sub-Sum
  -- t1 + t2 <: t1' + t2' 
  (tyₗ :+: tyᵣ) → case locty' of
    (ty'ₗ :+: ty'ᵣ) → do 

        meet_tyₗ  ← (ty_meet tyₗ ty'ₗ)
        meet_tyᵣ ← (ty_meet tyᵣ ty'ᵣ)
        return (meet_tyₗ :+: meet_tyᵣ)
    _ → return False 
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
        guardErr (l ≡ l') $
          typeError "meet: l ≢ l'" $ frhs
            [ ("l", pretty l)
            , ("l'", pretty l')
            ]
        join_τ₁₁ ← (locty_join τ₁₁ τ₁₁')
        meet_τ₁₂ ← (locty_meet τ₁₂ τ₁₂')
        return (join_τ₁₁ :→: (η :* meet_τ₁₂))

  (RefT None τ)  →  case locty' of
    (RefT _ τ') → do
        loc_meet ← (locty_meet locty locty')
        return (RefT None loc_meet)
    _  → todoError
  (RefT (Some loc) τ)  →  case locty' of
      (RefT None τ') → do
        loc_meet ← (locty_meet locty locty')
        return (RefT None loc_meet)
      _  → if (locty == locty') then (return locty) else todoError
  (ArrT None n τ)  →  case locty' of
    (ArrT _ _ τ') → do
        loc_meet ← (locty_meet locty locty')
        return (RefT None loc_meet)
    _  → todoError
  (ArrT (Some loc) n τ)  →  case locty' of
      (ArrT None _ τ') → do
        loc_meet ← (locty_meet locty locty')
        return (ArrT None n loc_meet)
      _  → if (locty == locty') then (return locty) else todoError
  (ISecT loc loc_ty) →  case locty' of
      (ISecT loc' loc_ty') → do 
        loc_union ← (union_em loc loc')
        loc_meet ← (locty_meet loc_ty loc_ty')
        return (ISecT loc_union loc_meet)
      ty' → todoError
  _ → todoError

-- Finds join of two types
ty_meet :: Type  → Type  → EM Type 
ty_meet ty ty' = case ty of
  SecT loc loc_ty → (case ty' of
      SecT loc' loc_ty' → do 
        loc_union ← (union_em loc loc')
        loc_meet ← (locty_meet loc_ty loc_ty')
        return (SecT loc_union loc_meet)
      ty' → todoError)

  x  → todoError

-- Finds join of two located types
locty_join :: Type  → Type  → EM Type 
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
  ShareT p loc locty  → (case locty' of
    ShareT p' loc' locty' → 
      do 
        l ← (elabEMode loc)
        l' ← (elabEMode loc')
        if ((p == p') ⩓ (l == l'))
          then (
            do
              loc_join ← (locty_join locty locty')
              return (ShareT p loc loc_join)
          )
        else todoError
      
    _  → todoError
    )
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
        guardErr (l ≡ l') $
          typeError "join: l ≢ l'" $ frhs
            [ ("l", pretty l)
            , ("l'", pretty l')
            ]
        meet_τ₁₁ ← (locty_meet τ₁₁ τ₁₁')
        join_τ₁₂ ← (locty_join τ₁₂ τ₁₂')
        return (meet_τ₁₁ :→: (η :* join_τ₁₂))

  (RefT None τ)  →  case locty' of
    (RefT locO τ') → do
        loc_join ← (locty_join locty locty')
        return (RefT locO loc_join)
    _  → todoError
  (RefT (Some loc) τ)  →  case locty' of
      (RefT None τ') → do
        loc_join ← (locty_join locty locty')
        return (RefT (Some loc) loc_join)
      _  → if (locty == locty') then (return locty) else todoError
  (ArrT None n τ)  →  case locty' of
    (ArrT locO _ τ') → do
        loc_join ← (locty_join locty locty')
        return (ArrT locO n loc_join)
  (ArrT (Some loc) n τ)  →  case locty' of
    (ArrT None _ τ') → do
        loc_join ← (locty_join locty locty')
        return (ArrT (Some loc) n loc_join)
    _  → if (locty == locty') then (return locty) else todoError
  (ISecT loc loc_ty) → case locty' of
      (ISecT loc' loc_ty') → do 
        loc_inter ← (inter_em loc loc')
        loc_top ← (locty_join loc_ty loc_ty')
        return (SecT loc_inter loc_top)
      _ → todoError
  _ → todoError

-- Finds join of two types
ty_join :: Type  → Type  → EM Type 
ty_join ty ty' = case ty of
  SecT loc loc_ty → case ty' of
      SecT loc' loc_ty' → do 
        loc_inter ← (inter_em loc loc')
        loc_top ← (locty_join loc_ty loc_ty')
        return (SecT loc_inter loc_top)
      _ → todoError

  x  → todoError

-- Assumes non empty list of well-formed types
joinList :: 𝐿 Type → EM Type
joinList τs =
  case τs of 
    Nil → todoError
    τ :& τs → (mfold τ ty_join τs)

-----------------
--- Well formed fnctions functions ---
-----------------

-- Rules to see if any located value is well-formed
wf_loctype :: Type → Mode → EM ()
wf_loctype sigma m =
  case sigma of
     -- WF-Base (Based off WF-INT)
    BaseT bt → return () 
    ShareT p loc locty → do
      _ ← (wf_share_loctype locty m)
      l ← (elabEMode loc)
      -- WF-Enc
      return ()
    -- WF-Sum: t1 must be well formed and t2 must be well formed
    (loctyₗ :+: loctyᵣ) → do 
      _ ← (wf_type loctyₗ m)
      _ ← (wf_type loctyᵣ m)
      return ()
    -- WF-Prod: t1 must be well formed and t2 must be well formed
    (loctyₗ :×: loctyᵣ)  → do
      _ ← (wf_type loctyₗ m)
      _ ← (wf_type loctyᵣ m)
      return ()
    (ListT _ τₜ)  → do
      _ ← (wf_type τₜ m)
      return ()
    -- WF-Fun: m must be same as mode, t1 must be well formed and t2 must be well formed
    (τ₁₁ :→: (η :* τ₁₂)) → do
      m  ← askL terModeL
      l ← elabEMode $ effectMode η
      _ ← (wf_type τ₁₁ m)
      _ ← (wf_type τ₁₂ m)
      guardErr (m ≡ l) $
        typeError "Not well formed m != l" $ frhs
        [ ("m", pretty m)
        , ("l", pretty l)
        ]
      return ()
    (RefT _ τ')  → do
      _ ← (wf_type τ' m)
      return ()
    (ArrT _ _ τ')  →  do
      _ ← (wf_type τ' m)
      return ()
    ISecT loc locty → do
      _ ← (wf_share_loctype locty m)
      return ()
    _  → todoError


-- Rules to see if some located value is well-formed
wf_share_loctype :: Type → Mode → EM ()
wf_share_loctype sigma m =
  case sigma of
    BaseT bt → return () 
    (loctyₗ :+: loctyᵣ) → do 
      _ ← (wf_type loctyₗ m)
      _ ← (wf_type loctyᵣ m)
      return ()
    _  → do
      todoError


-- Rules to see if the type is well formed
wf_type :: Type → Mode → EM ()
wf_type ty m = 
  case ty of 

    -- WF-Loc
    SecT em' locty → do
      m' ← (elabEMode em')
      wfcond ← (wf_loctype locty m')
      guardErr (supermode m m') $
        typeError "m is not a superet of m'" $ frhs
        [ ("m", pretty m)
        , ("m'", pretty m')
        ]
      return ()
    _ → todoError


-- Rules to get the least sub subtype of loctype sigma that is well formed
sublocty_wf :: Type  → Mode →  EM Type 
sublocty_wf sigma m = 
  case sigma of
    -- WF-Base (Based off WF-INT)
    BaseT bt → return sigma
    ShareT p loc loc_ty  → do
        l ← (elabEMode loc)
        if (l == m) then
          do 
            loc_subty ← (share_subloctype_wf loc_ty m)
            return (ShareT p loc loc_subty)
        else
          todoError
    -- WF-Sum: t1 must be well formed and t2 must be well formed
    (loctyₗ :+: loctyᵣ) → do 
      loctyₗ' ← (subty_wf loctyₗ m)
      loctyᵣ' ← (subty_wf loctyᵣ m)
      return (loctyₗ' :+: loctyᵣ')
    (loctyₗ :×: loctyᵣ)  → do
      loctyₗ' ← (subty_wf loctyₗ m)
      loctyᵣ' ← (subty_wf loctyᵣ m)
      return (loctyₗ' :×: loctyᵣ')
    (ListT n τₜ)  → do
      τₜ' ← (subty_wf τₜ m)
      return (ListT n τₜ') 
    -- WF-Fun: m must be same as mode, t1 must be well formed and t2 must be well formed
    (τ₁₁ :→: (η :* τ₁₂)) → do
      l ← elabEMode $ effectMode η
      guardErr (m ≡ l) $
        typeError "Not well formed m != l" $ frhs
        [ ("m", pretty m)
        , ("l", pretty l)
        ]
      τ₁₁' ← (superty_wf τ₁₁ m)
      τ₁₂' ← (subty_wf τ₁₂ m)
      return (τ₁₁' :→:  (η :* τ₁₂'))
    (RefT loc τ)  → do
      τ' ← (subty_wf τ m)
      return (RefT loc τ')
    (ArrT loc n τ)  → do
      τ' ← (subty_wf τ m)
      return (ArrT loc n τ')
    (ISecT loc loc_ty) → do
      loc_subty ← (share_subloctype_wf loc_ty m)
      (return (ISecT loc loc_subty))
    x  → todoError

-- Rules to get the least super supertype of located type that a share can take sigma that is well formed
share_subloctype_wf :: Type → Mode → EM Type
share_subloctype_wf sigma m =
  case sigma of
    BaseT bt → return sigma
    (loctyₗ :+: loctyᵣ) → do 
      loctyₗ' ← (subty_wf loctyₗ m)
      loctyᵣ' ← (subty_wf loctyᵣ m)
      return (loctyₗ' :+: loctyᵣ')
    _  → todoError

-- Rules to get the least super supertype of type t that is well formed
subty_wf :: Type  → Mode  → EM Type 
subty_wf t m = 
    case t of
    SecT loc loc_ty → do
      m' ← (elabEMode loc)
      loc_subty ← (superlocty_wf loc_ty m')
      guardErr (supermode m m') $
        typeError "m is not a superset of m'" $ frhs
        [ ("m", pretty m)
        , ("m'", pretty m')
        ]
      (return (SecT loc loc_subty))
    _  → todoError


-- Rules to get the least super supertype of loctype sigma that is well formed
superlocty_wf :: Type  → Mode →  EM Type 
superlocty_wf sigma m = 
  case sigma of
    -- WF-Base (Based off WF-INT)
    BaseT bt → return sigma
    ShareT p loc loc_ty  → do
        l ← (elabEMode loc)
        if (l == m) then
          do 
            loc_superty ← (share_superloctype_wf loc_ty m)
            return (ShareT p loc loc_superty)
        else
          todoError
    -- WF-Sum: t1 must be well formed and t2 must be well formed
    (loctyₗ :+: loctyᵣ) → do 
      loctyₗ' ← (superty_wf loctyₗ m)
      loctyᵣ' ← (superty_wf loctyᵣ m)
      return (loctyₗ' :+: loctyᵣ')
    (loctyₗ :×: loctyᵣ)  → do
      loctyₗ' ← (superty_wf loctyₗ m)
      loctyᵣ' ← (superty_wf loctyᵣ m)
      return (loctyₗ' :×: loctyᵣ')
    (ListT n τₜ)  → do
      τₜ' ← (superty_wf τₜ m)
      return (ListT n τₜ') 
    -- WF-Fun: t1 must be well formed and t2 must be well formed
    (τ₁₁ :→: (η :* τ₁₂)) → do
      l ← elabEMode $ effectMode η
        guardErr (m ≡ l) $
          typeError "Not well formed m != l" $ frhs
          [ ("m", pretty m)
            , ("l", pretty l)
          ]
      τ₁₁' ← (subty_wf τ₁₁ m)
      τ₁₂' ← (superty_wf τ₁₂ m)
      return (τ₁₁' :→:  (η :* τ₁₂'))
    (RefT loc τ)  → do
      τ' ← (superty_wf τ m)
      return (RefT loc τ')
    (ArrT loc n τ)  → do
      τ' ← (superty_wf τ m)
      return (ArrT loc n τ')
    (ISecT loc loc_ty) → do
      loc_subty ← (share_superloctype_wf loc_ty m)
      (return (ISecT loc loc_subty))
    _  → todoError

-- Rules to get the least super supertype of located type that a share can take sigma that is well formed
share_superloctype_wf :: Type → Mode → EM Type
share_superloctype_wf sigma m =
  case sigma of
    BaseT bt → return sigma
    (loctyₗ :+: loctyᵣ) → do 
      loctyₗ' ← (superty_wf loctyₗ m)
      loctyᵣ' ← (superty_wf loctyᵣ m)
      return (loctyₗ' :+: loctyᵣ')
    _  → todoError

-- Rules to get the least super supertype of type t that is well formed
superty_wf :: Type  → Mode  → EM Type 
superty_wf t m = 
    case t of
    SecT loc loc_ty → do
        l ← (elabEMode loc)
        l_inter ← (elabMode (inter_m m l))
        loc_superty ← (superlocty_wf loc_ty m)
        return (SecT l_inter loc_superty)
    _  → todoError


-----------------
--- Bind Typing ---
-----------------

-- Maps a type to a variable in the context
bindTo ∷ Var → Type → EM a → EM a
bindTo x τ = mapEnvL terEnvL ((x ↦ τ) ⩌)

-- Returns a function that will change the environment based on the pattern
bindType ∷ Type → Pat → (EM (EM a → EM a))
bindType τ ψ = matchType τ ψ

-- assume type is well formed to the current m
matchType ∷  Type → Pat → EM (EM a → EM a)
matchType τ ψ= case ψ of 
  VarP x → return (bindTo  x τ)
  BulP → case τ of
    (SecT loc (BaseT (UnitT) )) →  do
          m ← askL terModeL
          l ← elabEMode loc
          guardErr (m ≡ l) $
            typeError "matchType: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
              , ("l", pretty l)
              ] 
          return id
    (SecT loc (ShareT _ _ (BaseT (UnitT) ))) →  do
          m ← askL terModeL
          l ← elabEMode loc
          guardErr (m ≡ l) $
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
          guardErr (m ≡ l) $
            typeError "matchType: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
              , ("l", pretty l)
              ] 
          return id
    (SecT loc (ShareT _ _ (BaseT  ℙsT )))   → do 
          m ← askL terModeL
          l ← elabEMode loc
          guardErr (m ≡ l) $
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
          guardErr (m ≡ l) $
            typeError "matchType: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
              , ("l", pretty l)
              ] 
          return (\y -> ( 
            do
            mt ← (bindType  (SecT loc (BaseT ℙsT )) ψ)
            (mt  ((bindTo  x (SecT loc (BaseT ℙT ))) y)) ))
    (SecT loc (ShareT p loc' (BaseT  ℙsT )))  → do
          m ← askL terModeL
          l ← elabEMode loc
          guardErr (m ≡ l) $
            typeError "matchType: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
              , ("l", pretty l)
              ] 
          return (\y -> ( 
            do
            mt ←  (bindType (SecT loc (ShareT p loc' (BaseT ℙsT ))) ψ)
            (mt ((bindTo  x (SecT loc (ShareT p loc' (BaseT ℙT )))) y) ) ))
    _ → typeError "matchType: ⊢ₘ _ ˡ→ _ ; the expression is not of type SecT loc τ" $ frhs
              [ ("τ", pretty (BaseT ℙsT ))
              ] 
  ProdP ψₗ ψᵣ  →     case τ of
    (SecT loc (τₗ :×: τᵣ)) → do
        m ← askL terModeL
        l ← elabEMode loc
        guardErr (m ≡ l) $
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
        guardErr (m ≡ l) $
          typeError "matchType: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
              , ("l", pretty l)
              ] 
           (bindType τₗ ψₗ)
    (SecT loc (ShareT _ _ (τₗ  :+: _))) → do
        m ← askL terModeL
        l ← elabEMode loc
        guardErr (m ≡ l) $
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
        guardErr (m ≡ l) $
          typeError "matchType: ⊢ₘ _ ˡ→ _ ; m ≢ l" $ frhs
              [ ("m", pretty m)
              , ("l", pretty l)
              ] 
           (bindType τᵣ ψᵣ)
    (SecT loc (ShareT _ _ (τₗ  :+: τᵣ))) → do
        m ← askL terModeL
        l ← elabEMode loc
        guardErr (m ≡ l) $
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
          guardErr (m ≡ l) $
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
          guardErr (m ≡ l) $
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
  WildP → return id
------------------------------------------------
-- Static Evaluation of Principal Expressions --
------------------------------------------------
setToList :: (𝑃 a)  → (𝐿 a)
setToList myset = list𝐼 (iter myset)

listToSet :: (Ord a) ⇒ (𝐿 a)  → (𝑃 a)
listToSet mylist = pow𝐼 (iter mylist)

elabPrinExp ∷ PrinExp → EM PrinVal
elabPrinExp ρe = case  ρe of
  VarPE x       → return (SinglePV (𝕩name x))
  AccessPE x n₁ → return (AccessPV (𝕩name x) n₁)

elabPrinSetExp ∷ PrinSetExp → EM (𝑃 PrinVal)
elabPrinSetExp ρse = case  ρse of
  PowPSE ρel → do
    pvl ← (mapM elabPrinExp ρel )
    (let ρvs = (listToSet pvl) in (return ρvs))
 
  x → todoError


elabEMode ∷ EMode → EM Mode
elabEMode = mapM elabPrinSetExp

elabPrinVal :: PrinVal → EM PrinExp
elabPrinVal ρv = case  ρv of
  (SinglePV ρ)    → return (VarPE (var ρ)) 
  (AccessPV ρ n₁) → return (AccessPE (var ρ) n₁)


    
-- turn powerset to list, map the list, convert to prinsetexp
elabPrinValSet :: (𝑃 PrinVal)  → EM PrinSetExp
elabPrinValSet ρvp = let ρvl = (setToList ρvp) in do
  ρel ← (mapM elabPrinVal ρvl) 
  (return (PowPSE ρel))

elabMode ∷ Mode → EM EMode
elabMode = mapM elabPrinValSet