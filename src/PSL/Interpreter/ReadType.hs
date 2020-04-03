module PSL.Interpreter.ReadType where

import UVMHS
import AddToUVMHS

import Paths_psl

import PSL.Syntax

import PSL.Interpreter.Types
import PSL.Interpreter.Truncating
import PSL.Interpreter.Access

import qualified Text.Read as HS

primRead ∷ (HS.Read a) ⇒ 𝕊 → 𝑂 (𝕊 ∧ a)
primRead s = case HS.reads $ chars s of
  [(x,s')] → Some $ string s' :* x
  _ → None

prinDataPath ∷ PrinVal → 𝕊
prinDataPath = \case
  SinglePV s → s
  AccessPV s i → s ⧺ "_" ⧺ show𝕊 i

parseInputType ∷ (STACK) ⇒ PrinVal → Type → 𝕊 → IM (𝕊 ∧ Val)
parseInputType ρ τ s = case τ of
  ℤT pr → do
    s' :* i ← error𝑂 (primRead @ ℤ s) $
      throwIErrorCxt TypeIError "parseInputType: ℤT: could not parse" null
    return $ (s' :*) $ IntV pr $ trPrInt pr i
  𝔽T pr → do
    s' :* d ← error𝑂 (primRead @ 𝔻 s) $
      throwIErrorCxt TypeIError "parseInputType: 𝔻T: could not parse" null
    return $ (s' :*) $  FltV pr d
  𝔹T → do
    s' :* b ← error𝑂 (primRead @ 𝔹 s) $
      throwIErrorCxt TypeIError "parseInputType: 𝔹T: could not parse" null
    return $ (s' :*) $ BoolV b
  ListT τ' → do
    vs ← mapM (snd ^∘ parseInputType ρ τ') $ list $ filter (≢ "") $ splitOn𝕊 "\n" s
    return $ (null :*) $ foldrOnFrom vs NilV $ \ v₁ v₂ → ConsV (SSecVP (single ρ) v₁) $ SSecVP (single ρ) v₂
  τ₁ :×: τ₂ → do
    s'  :* v₁ ← parseInputType ρ τ₁ s
    s'' :* v₂ ← parseInputType ρ τ₂ s'
    return $ (s'' :*) $ PairV (SSecVP (single ρ) v₁) $ SSecVP (single ρ) v₂
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
  snd ^$ parseInputType ρ τA *$ io $ read path

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
