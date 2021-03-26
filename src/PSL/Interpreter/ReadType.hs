module PSL.Interpreter.ReadType where

import UVMHS

import PSL.Config
import PSL.Syntax

import PSL.Interpreter.Val
import PSL.Interpreter.Truncating
import PSL.Interpreter.Types
import PSL.Interpreter.Lens
import PSL.Interpreter.Error

import qualified Text.Read as HS

primRead ∷ (HS.Read a) ⇒ 𝕊 → 𝑂 (𝕊 ∧ a)
primRead s = case HS.reads $ chars s of
  [(x,s')] → Some $ string s' :* x
  _ → None

prinDataPath ∷ PrinVal → IM 𝕊
prinDataPath = \case
  SinglePV s → return s
  AccessPV s i → return $ s ⧺ "_" ⧺ show𝕊 i
  VirtualPV s → throwIErrorCxt TypeIError "prinDataPath: i/o not allowed for virtual party s" $ frhs
    [("s",pretty s)]

parseInputType ∷ (STACK) ⇒ PrinVal → Type → 𝕊 → IM (𝕊 ∧ Val)
parseInputType ρ τ s = case τ of
  BaseT (ℤT pr) → do
    s' :* i ← error𝑂 (primRead @ ℤ s) $
      throwIErrorCxt TypeIError "parseInputType: ℤT: could not parse" null
    return $ (s' :*) $ BaseV $ IntBV pr $ trPrInt pr i
  BaseT (𝔽T pr) → do
    s' :* d ← error𝑂 (primRead @ 𝔻 s) $
      throwIErrorCxt TypeIError "parseInputType: 𝔻T: could not parse" null
    return $ (s' :*) $ BaseV $ FltBV pr d
  BaseT 𝔹T → do
    s' :* b ← error𝑂 (primRead @ 𝔹 s) $
      throwIErrorCxt TypeIError "parseInputType: 𝔹T: could not parse" null
    return $ (s' :*) $ BaseV $ BoolBV b
  ListT τ' → do
    vs ← mapM (snd ^∘ parseInputType ρ τ') $ list $ filter (≢ "") $ splitOn𝕊 "\n" s
    return $ (null :*) $ foldrOnFrom vs NilV $ \ v₁ v₂ → ConsV (SSecVP (SecM (single ρ)) v₁) $ SSecVP (SecM (single ρ)) v₂
  τ₁ :×: τ₂ → do
    s'  :* v₁ ← parseInputType ρ τ₁ s
    s'' :* v₂ ← parseInputType ρ τ₂ s'
    return $ (s'' :*) $ PairV (SSecVP (SecM (single ρ)) v₁) $ SSecVP (SecM (single ρ)) v₂
  ℙT → do
    kinds ← askL iCxtDeclPrinsL
    s' :* l ← error𝑂
      (case primRead @ HS.Lexeme s of
         Some (s' :* HS.Ident n) → Some (s' :* string n)
         _ → None
      ) $
      throwIErrorCxt TypeIError "parseInputType: ℙT: could not parse" null
    (s' :*) ∘ PrinV ^$ case tohs $ list $ splitOn𝕊 "_" l of
      [ρ'] → case kinds ⋕? ρ' of
        Some ρv → return $ case ρv of
          SinglePK → ValPEV $ SinglePV ρ'
          SetPK n → SetPEV n ρ'
          VirtualPK → ValPEV $ VirtualPV ρ'
        _ → throwIErrorCxt TypeIError "parseInputType: ℙT: [ρ']: kinds ⋕? ρ' ≢ Some _" $ frhs
          [ ("kinds",pretty kinds)
          , ("ρ'",pretty ρ')
          ]
      [ρ',iS] → case (kinds ⋕? ρ',frhs $ HS.readMaybe $ chars iS) of
        (Some ρκ,Some i) → case ρκ of
          SetPK n | i < n → return $ ValPEV $ AccessPV ρ' i
          _ → throwIErrorCxt TypeIError "parseInputType: ℙT: [ρ',iS]: (Some _,Some _): ρκ ≢ SetPK n | i < n" $ frhs
            [ ("ρκ",pretty ρκ)
            , ("i",pretty i)
            ]
        _ → throwIErrorCxt TypeIError "parseInputType: ℙT: [ρ',iS]: (kinds ≡? ρ',read iS) ≢ (Some _,Some _)" $ frhs
          [ ("kinds",pretty kinds)
          , ("ρ'",pretty ρ')
          , ("iS",pretty iS)
          ]
      _ → throwIErrorCxt TypeIError "parsseInputType" null
  _ → throwIErrorCxt NotImplementedIError "parseInputType" $ frhs
    [ ("τ",pretty τ)
    ]

readType ∷ (STACK) ⇒ PrinVal → Type → 𝕊 → IM Val
readType ρ τA fn = do
  b ← askL iCxtIsExampleL
  ppath ← prinDataPath ρ
  path ←
    if b
    then io $ do
      let relativePath = concat ["examples-input/",ppath,"/",fn]
      dataFilePath ← datapath relativePath
      relativePathExists ← pexists relativePath
      dataFilePathExists ← pexists dataFilePath
      when (not relativePathExists ⩓ dataFilePathExists) $ do
        dtouch $ concat ["examples-input/",ppath]
        fcopy dataFilePath relativePath
      return relativePath
    else return $ concat ["data-input/",ppath]
  snd ^$ parseInputType ρ τA *$ io $ fread path

serializeBaseVal ∷ BaseVal → 𝐼 𝕊
serializeBaseVal = \case
  BoolBV b → single $ show𝕊 b
  NatBV _ n → single $ show𝕊 n
  IntBV _ i → single $ show𝕊 i
  FltBV _ d → single $ show𝕊 d

serializeVal ∷ Val → IM (𝐼 𝕊)
serializeVal = \case
  BaseV bv → return $ serializeBaseVal bv
  PairV ṽ₁ ṽ₂ → do
    v₁ ← elimValP ṽ₁
    v₂ ← elimValP ṽ₂
    s₁ ← serializeVal v₁
    s₂ ← serializeVal v₂
    return $ concat [s₁,single "\n",s₂]
  ConsV ṽ₁ ṽ₂ → do
    v₁ ← elimValP ṽ₁
    v₂ ← elimValP ṽ₂
    s₁ ← serializeVal v₁
    s₂ ← serializeVal v₂
    return $ concat [s₁,single "\n",s₂]
  NilV → return null
  PrinV (ValPEV ρv) → case ρv of
    SinglePV ρ → return $ single ρ
    AccessPV ρ n → return $ single $ concat [ρ,".",show𝕊 n]
    VirtualPV ρ → return $ single ρ
  v → throwIErrorCxt NotImplementedIError "serializeVal" $ frhs
    [ ("v", pretty v) ]

writeVal ∷ (STACK) ⇒ PrinVal → Val → 𝕊 → IM ()
writeVal ρ v fn = do
  b ← askL iCxtIsExampleL
  ppath ← prinDataPath ρ
  let path =
        if b
        then concat ["examples-output/",ppath,"/",fn]
        else concat ["data-output/",ppath,"/",fn]
  io $ dtouch $ pdirectory path
  o ← concat ^$ serializeVal v
  io $ fwrite path o
