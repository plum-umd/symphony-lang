module Symphony.Dynamic.Par.ReadType where

import Symphony.Prelude

import Symphony.Config
import Symphony.Lang.Syntax

import Symphony.Dynamic.Par.Types
import Symphony.Dynamic.Par.Error
import Symphony.Dynamic.Par.Dist

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
inputPath ρ file = do
  ρPath ← prinDataPath ρ
  io $ findFile $ concat [ inputDir , "/", ρPath , "/", file ]
  where inputDir = "input"

outputPath ∷ (STACK) ⇒ PrinVal → 𝕊 → IM v 𝕊
outputPath ρ file = do
  ρPath ← prinDataPath ρ
  path  ← io $ findFile $ concat [ outputDir, "/", ρPath, "/", file ]
  io $ dtouch $ pdirectory path
  return path
  where outputDir = "output"

parseBaseVal ∷ (STACK) ⇒ BaseType → 𝕊 → IM v (𝕊 ∧ BaseVal)
parseBaseVal bτ s = case bτ of
  UnitT → do
    s' :* () ← error𝑂 (primRead @() s) $
               throwIErrorCxt TypeIError "parseInputType: UnitT: could not parse" null
    return $ s' :* BulV
  𝔹T    → do
    s' :* b ← error𝑂 (primRead @𝔹 s) $
              throwIErrorCxt TypeIError "parseInputType: 𝔹T: could not parse" $ frhs [ ("s", pretty s) ]
    return $ s' :* (BoolV $ ClearBV b)
  ℕT pr → do
    s' :* n ← error𝑂 (primRead @ℕ s) $
              throwIErrorCxt TypeIError "parseInputType: ℕT: could not parse" null
    return $ s' :* (NatV pr $ ClearNV n)
  ℤT pr → do
    s' :* z ← error𝑂 (primRead @ℤ s) $
              throwIErrorCxt TypeIError "parseInputType: ℤT: could not parse" null
    return $ s' :* (IntV pr $ ClearZV z)
  𝕊T    → todoCxt
  ℙT    → todoCxt
  ℙsT   → todoCxt

parseInputType ∷ (STACK) ⇒ Type → 𝕊 → IM Val (𝕊 ∧ Val)
parseInputType τ s = case τ of
  BaseT bτ → do
    s' :* bv ← parseBaseVal bτ s
    ṽ ← introValDist $ BaseV bv
    return $ s' :* ṽ
  ListT τ' → do
    ṽs ← mapM (snd ^∘ parseInputType τ') $ list $ filter (not ∘ isEmpty) $ splitOn𝕊 "\n" s
    (null :*) ^$ introValDist $ ListV ṽs
  ArrT τ' → do
    ṽs ← mapM (snd ^∘ parseInputType τ') $ list $ filter (not ∘ isEmpty) $ splitOn𝕊 "\n" s
    a ← io $ new𝕍Mut $ count ṽs
    eachOn (withIndex ṽs) $ \ (i :* ṽᵢ) → io $ set𝕍Mut i ṽᵢ a
    m ← askL iCxtModeL
    (null :*) ^$ introValDist $ LocV m (Inr a)
  τ₁ :×: τ₂ → do
    s'  :* ṽ₁ ← parseInputType τ₁ s
    s'' :* ṽ₂ ← parseInputType τ₂ s'
    (s'' :*) ^$ introValDist $ ProdV ṽ₁ ṽ₂
  _ → todoCxt
