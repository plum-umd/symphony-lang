module PSL.Interpreter.ReadType where

import UVMHS
import AddToUVMHS

import Paths_psl

import PSL.Syntax

import PSL.Interpreter.Types
import PSL.Interpreter.Truncating
import PSL.Interpreter.Access

import qualified Text.Read as HS

prinDataPath ∷ PrinVal → 𝕊
prinDataPath = \case
  SinglePV s → s
  AccessPV s i → s ⧺ "_" ⧺ show𝕊 i

parseInputType ∷ (STACK) ⇒ PrinVal → Type → 𝕊 → IM Val
parseInputType ρ τ s = case τ of
  ℤT pr → do
    let i = HS.read $ chars s ∷ ℤ
    return $ IntV pr $ trPrInt pr i
  𝔽T pr → do
    let d = HS.read $ chars s ∷ 𝔻
    return $ FltV pr d
  𝔹T → do
    let b = HS.read $ chars s ∷ 𝔹
    return $ BoolV b
  ListT τ' → do
    vs ← mapM (parseInputType ρ τ') $ list $ filter (≢ "") $ splitOn𝕊 "\n" s
    return $ foldrOnFrom vs NilV $ \ v₁ v₂ → ConsV (SSecVP (single ρ) v₁) $ SSecVP (single ρ) v₂
  ℙT → do
    kinds ← askL iCxtDeclPrinsL
    PrinV ^$ case tohs $ list $ splitOn𝕊 "_" s of
      [ρ'] → case kinds ⋕? ρ' of
        Some ρκ → return $ case ρκ of
          SinglePK → ValPEV $ SinglePV ρ'
          SetPK n → SetPEV n ρ'
        None → throwIErrorCxt TypeIError "parseInputType: ℙT: [ρ']: kinds ⋕? ρ' ≢ Some _" $ frhs
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
  path ← 
    if b
    then io $ string ^$ getDataFileName $ chars $ concat ["examples-input/",prinDataPath ρ,"/",fn]
    else return $ concat ["data-input/",prinDataPath ρ,"/",fn]
  parseInputType ρ τA *$ io $ read path

serializeVal ∷ Val → IM (𝐼 𝕊)
serializeVal = \case
  IntV _ i → return $ single $ show𝕊 i
  NatV _ n → return $ single $ show𝕊 n
  BoolV b → return $ single $ show𝕊 b
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
  v → throwIErrorCxt NotImplementedIError "serializeVal" $ frhs
    [ ("v",pretty v) ]

writeVal ∷ (STACK) ⇒ PrinVal → Val → 𝕊 → IM ()
writeVal ρ v fn = do
  b ← askL iCxtIsExampleL
  let path =
        if b
        then concat ["examples-output/",prinDataPath ρ,"/",fn]
        else concat ["data-output/",prinDataPath ρ,"/",fn]
  io $ touchDirs $ pathDir path
  o ← concat ^$ serializeVal v
  io $ write path o
