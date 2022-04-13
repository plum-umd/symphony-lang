module Symphony.Dynamic.Seq.Yao where

import Symphony.Prelude

import Symphony.Lang.Syntax

import Symphony.Dynamic.Seq.Error
import Symphony.Dynamic.Seq.Types
import Symphony.Dynamic.Seq.BaseVal.Types
import Symphony.Dynamic.Seq.Dist.Types
import Symphony.Dynamic.Seq.Lens

import Symphony.Dynamic.Seq.Send
import Symphony.Dynamic.Seq.EMP

import qualified Prelude as HS

empPublic ∷ ℤ8
empPublic = HS.fromIntegral 0

whoAmI ∷ IM DistVal PrinVal
whoAmI = fromSomeCxt *$ askL iCxtMeL

otherParty ∷ 𝑃 PrinVal → IM DistVal PrinVal
otherParty ρs = do
  me ← whoAmI
  fromSomeCxt $ view one𝑃L $ ρs ∖ (single𝑃 me)

empChan ∷ 𝑃 PrinVal → IM DistVal Channel
empChan ρs = do
  them ← otherParty ρs
  getOrMkChannel them

empParty ∷ 𝑃 PrinVal → IM DistVal ℤ8
empParty ρs = do
  me  ← whoAmI
  ids ← fromSomeCxt $ map (dict𝐼 ∘ iter) $ zipSameLength (list ρs) (frhs [1..(count ρs)])
  fromSomeCxt $ HS.fromIntegral ^$ ids ⋕? me

getEMPSession ∷ 𝑃 PrinVal → IM DistVal (𝑂 EMPProtocol)
getEMPSession ρs = do
  πs ← getL iStateSessionsYaoL
  return $ πs ⋕? ρs

mkEMPSession ∷ 𝑃 PrinVal → IM DistVal EMPProtocol
mkEMPSession ρs = do
  chan  ← empChan ρs
  party ← empParty ρs
  π     ← empSemiCtxCreate party chan
  modifyL iStateSessionsYaoL ((ρs ↦ π) ⩌!)
  return π

getOrMkEMPSession ∷ 𝑃 PrinVal → IM DistVal EMPProtocol
getOrMkEMPSession ρs = do
  π𝑂 ← getEMPSession ρs
  case π𝑂 of
    None   → mkEMPSession ρs
    Some π → return π

instance Protocol 'Yao2P where
  type Share 'Yao2P = EMPVal

  sendShare ∷ SProt 'Yao2P → 𝑃 Channel → ClearBaseVal → IM DistVal ()
  sendShare _ toChans v =
    case v of
      BoolV b → empSemiBitSendShare b (list toChans)
      _       → todoCxt

  recvShare ∷ SProt 'Yao2P → 𝑃 PrinVal → Channel → BaseType → IM DistVal EMPVal
  recvShare _ ρs frChan τ = do
    π ← getOrMkEMPSession ρs
    case τ of
      𝔹T → BoolEV ^$ empSemiBitRecvShare π frChan
      _  → todoCxt

  embed ∷ SProt 'Yao2P → 𝑃 PrinVal → ClearBaseVal → IM DistVal EMPVal
  embed _ ρs v = do
    π ← getOrMkEMPSession ρs
    case v of
      BoolV b → BoolEV ^$ empSemiBitShare π empPublic b
      _       → todoCxt

  prim ∷ SProt 'Yao2P → 𝑃 PrinVal → Op → 𝐿 EMPVal → IM DistVal EMPVal
  prim _ ρs op v̂s = do
    π ← getOrMkEMPSession ρs
    case (op, tohs v̂s) of
      (PlusO, [BoolEV b̂₁, BoolEV b̂₂]) → BoolEV ^$ empSemiBitXor π b̂₁ b̂₂
      (AndO, [BoolEV b̂₁, BoolEV b̂₂]) → BoolEV ^$ empSemiBitAnd π b̂₁ b̂₂
      _                                → todoCxt

  sendReveal ∷ SProt 'Yao2P → 𝑃 PrinVal → Channel → EMPVal → IM DistVal ()
  sendReveal _ ρs toChan v̂ = do
    π ← getOrMkEMPSession ρs
    case v̂ of
      BoolEV b̂ → empSemiBitSendReveal π b̂ toChan
      _        → todoCxt

  recvReveal ∷ SProt 'Yao2P → 𝑃 Channel → BaseType → IM DistVal ClearBaseVal
  recvReveal _ frChans τ =
    case τ of
      𝔹T → BoolV ^$ empSemiBitRecvReveal (list frChans)
      _  → todoCxt
