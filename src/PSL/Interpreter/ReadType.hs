module PSL.Interpreter.ReadType where

import UVMHS

import Paths_psl

import PSL.Syntax

import PSL.Interpreter.Types
import PSL.Interpreter.Truncating

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
readType ρ τA fn = parseInputType ρ τA $ ioUNSAFE $ do
  path ← string ^$ getDataFileName $ chars $ "examples-data/" ⧺ prinDataPath ρ ⧺ "/" ⧺ fn
  read path
