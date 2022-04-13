module Symphony.Dynamic.Seq.SPDZ where
{-
import UVMHS
import AddToUVMHS

import Symphony.Syntax
import Symphony.Dynamic.Seq.Types
import Symphony.Dynamic.Seq.BaseVal
import Symphony.Dynamic.Seq.Dist.Types
import Symphony.Dynamic.Seq.Error
import Symphony.Dynamic.Seq.Lens (iStateSessionsSPDZL)
import Symphony.Dynamic.Seq.Truncating

import Symphony.Dynamic.Seq.MPSPDZ

import qualified Prelude as HS

instance Protocol 'SPDZP where
  type Share 'SPDZP = MPSPDZVal

  share ∷ P 'SPDZP → PrinVal → 𝑃 PrinVal → (ClearBaseVal ∨ BaseType) → IM DistVal MPSPDZVal
  share _p = spdzShare

  embed ∷ P 'SPDZP → 𝑃 PrinVal → ClearBaseVal → IM DistVal MPSPDZVal
  embed _p = spdzEmbed

  prim ∷ P 'SPDZP → 𝑃 PrinVal → Op → 𝐿 MPSPDZVal → IM DistVal MPSPDZVal
  prim _p = spdzPrim

  reveal ∷ P 'SPDZP → 𝑃 PrinVal → PrinVal → MPSPDZVal → IM DistVal ClearBaseVal
  reveal _p = spdzReveal

spdzShare ∷ PrinVal → 𝑃 PrinVal → (ClearBaseVal ∨ BaseType) → IM DistVal MPSPDZVal
spdzShare ρvFr ρvsTo cbvorbτ = do
  spdzCheckShare ρvFr ρvsTo
  spdzp ← getOrMkSession ρvsTo
  let bvc = elimChoice id defaultClearBaseVal cbvorbτ
  prin ← spdzPrin ρvFr ρvsTo
  spdzShareVal spdzp (HS.fromIntegral prin) bvc

spdzCheckShare ∷ PrinVal → 𝑃 PrinVal → IM DistVal ()
spdzCheckShare ρvFr ρvsTo = do
  guardErr (ρvFr ∈ ρvsTo) $
    throwIErrorCxt TypeIError "spdzCheckShare: ρvFr ∉ ρvsTo" $ frhs
    [ ("ρvFr", pretty ρvFr)
    , ("ρvsTo", pretty ρvsTo)
    ]

spdzCheckReveal ∷ 𝑃 PrinVal → PrinVal → IM DistVal ()
spdzCheckReveal ρvsFr ρvTo = do
  guardErr (ρvTo ∈ ρvsFr) $
    throwIErrorCxt TypeIError "spdzCheckReveal: ρvTo ∉ ρvsFr" $ frhs
    [ ("ρvTo", pretty ρvTo)
    , ("ρvsFr", pretty ρvsFr)
    ]

spdzShareVal ∷ MPSPDZProtocol → HS.Int → ClearBaseVal → IM DistVal MPSPDZVal
spdzShareVal spdzp party = \case
  IntV pr z | pr ≡ ipr64 → map IntMPSPDZV $ io $ mpspdzIntegerShare spdzp party $ HS.fromIntegral z
  _ → todoCxt

spdzEmbed ∷ 𝑃 PrinVal → ClearBaseVal → IM DistVal MPSPDZVal
spdzEmbed ρvsFrTo cbv = do
  spdzp ← getOrMkSession ρvsFrTo
  spdzEmbedVal spdzp cbv

spdzEmbedVal ∷ MPSPDZProtocol → ClearBaseVal → IM DistVal MPSPDZVal
spdzEmbedVal spdzp = \case
  IntV pr z | pr ≡ ipr64 → map IntMPSPDZV $ io $ mpspdzIntegerEmbed spdzp $ HS.fromIntegral z
  _ → todoCxt

spdzPrim ∷ 𝑃 PrinVal → Op → 𝐿 MPSPDZVal → IM DistVal MPSPDZVal
spdzPrim ρvsC op mpvs = do
  spdzp ← fromSomeCxt *$ getSession ρvsC
  case (op, tohs mpvs) of
    (TimesO, [ IntMPSPDZV mpz₁, IntMPSPDZV mpz₂ ]) → map IntMPSPDZV $ io $ mpspdzIntegerMult spdzp mpz₁ mpz₂
    _ → todoCxt

spdzReveal ∷ 𝑃 PrinVal → PrinVal → MPSPDZVal → IM DistVal ClearBaseVal
spdzReveal ρvsFr ρvTo mpv = do
  spdzCheckReveal ρvsFr ρvTo
  spdzp ← fromSomeCxt *$ getSession ρvsFr
  prin ← spdzPrin ρvTo ρvsFr
  spdzRevealVal spdzp (HS.fromIntegral prin) mpv

spdzRevealVal ∷ MPSPDZProtocol → HS.Int → MPSPDZVal → IM DistVal ClearBaseVal
spdzRevealVal spdzp party = \case
  IntMPSPDZV mpz → map ((IntV ipr64) ∘ (trPrInt ipr64) ∘ HS.fromIntegral) $ io $ mpspdzIntegerReveal spdzp party mpz
  _ → todoCxt

getSession ∷ 𝑃 PrinVal → IM DistVal (𝑂 MPSPDZProtocol)
getSession ρvsC = do
  sessions ← getL iStateSessionsSPDZL
  return $ sessions ⋕? ρvsC

spdzPrin ∷ PrinVal → 𝑃 PrinVal → IM DistVal ℕ
spdzPrin ρv ρvsC = do
  spdzIds ← fromSomeCxt $ map (dict𝐼 ∘ iter) $ zipSameLength (list ρvsC) (frhs [1..(count ρvsC)])
  fromSomeCxt $ spdzIds ⋕? ρv

mkSession ∷ 𝑃 PrinVal → IM DistVal MPSPDZProtocol
mkSession ρvsC = do
  ρvMe ← fromSomeCxt *$ askL iCxtMeL
  prin ← spdzPrin ρvMe ρvsC
  spdzp ← io $ mpspdzCreate (HS.fromIntegral prin) $ HS.fromIntegral (psize ρvsC)
  modifyL iStateSessionsSPDZL ((ρvsC ↦ spdzp) ⩌!)
  return spdzp

getOrMkSession ∷ 𝑃 PrinVal → IM DistVal MPSPDZProtocol
getOrMkSession ρvsC = do
  spdzp𝑂 ← getSession ρvsC
  case spdzp𝑂 of
    None      → mkSession ρvsC
    Some spdzp → return spdzp

ipr64 ∷ IPrecision
ipr64 = FixedIPr 64 0
-}
