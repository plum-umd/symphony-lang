module Symphony.Interpreter.ReadType where

import UVMHS
import AddToUVMHS

import Symphony.Config
import Symphony.Syntax

import Symphony.Interpreter.Types
import Symphony.Interpreter.BaseVal.Types
import Symphony.Interpreter.Error

import qualified Prelude as HS
import qualified Text.Read as R

prinDataPath ∷ PrinVal → IM v 𝕊
prinDataPath = \case
  SinglePV s   → return s
  AccessPV s n → return $ s ⧺ "_" ⧺ show𝕊 n

primRead ∷ (R.Read a) ⇒ 𝕊 → 𝑂 (𝕊 ∧ a)
primRead s = case HS.reads $ chars s of
  [(x, s')] → Some $ string s' :* x
  _         → None

inputPath ∷ (STACK) ⇒ PrinVal → 𝕊 → IM v 𝕊
inputPath ρ fn = do
  b ← askL iCxtIsExampleL
  ppath ← prinDataPath ρ
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

outputPath ∷ (STACK) ⇒ PrinVal → 𝕊 → IM v 𝕊
outputPath ρ fn = do
  b ← askL iCxtIsExampleL
  ppath ← prinDataPath ρ
  let path =
        if b
        then concat ["examples-output/",ppath,"/",fn]
        else concat ["data-output/",ppath,"/",fn]
  io $ dtouch $ pdirectory path
  return path

parseBaseVal ∷ (STACK) ⇒ BaseType → 𝕊 → IM v (𝕊 ∧ ClearBaseVal)
parseBaseVal bτ s = case bτ of
  UnitT → do
    s' :* () ← error𝑂 (primRead @() s) $
               throwIErrorCxt TypeIError "parseInputType: UnitT: could not parse" null
    return $ s' :* BulV
  𝔹T    → do
    s' :* b ← error𝑂 (primRead @𝔹 s) $
              throwIErrorCxt TypeIError "parseInputType: 𝔹T: could not parse" null
    return $ s' :* BoolV b
  ℕT pr → do
    s' :* n ← error𝑂 (primRead @ℕ s) $
              throwIErrorCxt TypeIError "parseInputType: ℕT: could not parse" null
    return $ s' :* NatV pr n
  ℤT pr → do
    s' :* z ← error𝑂 (primRead @ℤ s) $
              throwIErrorCxt TypeIError "parseInputType: ℤT: could not parse" null
    return $ s' :* IntV pr z
  𝔽T pr → do
    s' :* d ← error𝑂 (primRead @𝔻 s) $
              throwIErrorCxt TypeIError "parseInputType: 𝔽T: could not parse" null
    return $ s' :* FltV pr d
  𝕊T    → todoCxt
  ℙT    → todoCxt
  ℙsT   → todoCxt

parseInputType ∷ (STACK, Value v) ⇒ Type → 𝕊 → IM v (𝕊 ∧ v)
parseInputType τ s = case τ of
  BaseT bτ → do
    s' :* cbv ← parseBaseVal bτ s
    ṽ ← introVal $ BaseV $ Clear cbv
    return $ s' :* ṽ
  ListT _n τ' → do
    ṽs ← mapM (snd ^∘ parseInputType τ') $ list $ filter (not ∘ isEmpty) $ splitOn𝕊 "\n" s
    (null :*) ^$ introVal $ ListV ṽs
  ArrT _em n τ' → do
    ṽs ← mapM (snd ^∘ parseInputType τ') $ list $ filter (not ∘ isEmpty) $ splitOn𝕊 "\n" s
    a ← io $ new𝕍Mut (natΩ64 n)
    eachOn (withIndex ṽs) $ \ (i :* ṽᵢ) → io $ set𝕍Mut i ṽᵢ a
    m ← askL iCxtModeL
    (null :*) ^$ introVal $ LocV m (Inr a)
  τ₁ :×: τ₂ → do
    s'  :* ṽ₁ ← parseInputType τ₁ s
    s'' :* ṽ₂ ← parseInputType τ₂ s'
    (s'' :*) ^$ introVal $ ProdV ṽ₁ ṽ₂
  _ → todoCxt
