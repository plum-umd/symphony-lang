module PSL.Interpreter.YaoN where

import UVMHS
import AddToUVMHS

import PSL.Syntax
import PSL.Interpreter.Types
import PSL.Interpreter.Pretty ()
import PSL.Interpreter.Lens
import PSL.Interpreter.Error

import PSL.Interpreter.Circuits
import PSL.Interpreter.Bristol

import qualified Data.Text as Text
import qualified System.Process as Process

getParty ∷ IM PrinVal
getParty = do
  lm ← askL iCxtLocalModeL       -- Note: Local Mode, `lm`, is always either TopM or a singleton
  ρvs ← fromSomeCxt $ view secML lm --   TopM is impossible, since we are in the YaoN protocol (TopM always executes plaintext protocol -- i.e. sequential mode)
  fromSomeCxt $ view one𝑃L ρvs      --   ∴ `lm` is a singleton.

instance Protocol 'YaoNP where
  type ProtocolVal 'YaoNP = Ckt

  typeOf ∷ P 'YaoNP → Ckt → BaseType
  typeOf _p = cktType

  shareBaseVal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'YaoNP → PrinVal → 𝑃 PrinVal → BaseVal → m Ckt
  shareBaseVal _p = shareBaseValCkt

  shareUnk ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'YaoNP → PrinVal → 𝑃 PrinVal → BaseType → m Ckt
  shareUnk _p = shareUnkCkt

  embedBaseVal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'YaoNP → 𝑃 PrinVal → BaseVal → m Ckt
  embedBaseVal _p = embedBaseValCkt

  exePrim ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'YaoNP → 𝑃 PrinVal → Op → 𝐿 Ckt → m Ckt
  exePrim _p = exePrimCkt

  reveal ∷ (Monad m, MonadReader ICxt m, MonadError IError m, MonadState IState m, MonadIO m) ⇒ P 'YaoNP → 𝑃 PrinVal → PrinVal → MPCVal 'YaoNP → m Val
  reveal _p ρvs₁ ρv₂ v̂ = do
    pptraceM v̂
    bristol :* input :* outputSize ← toBristol (list ρvs₁) v̂
    io $ out "\n\nBristol Output\n"
    io $ out bristol
    io $ out "\n\nThis party's input\n"
    pptraceM input
    io $ out "\n\n"
    return $ BaseV $ BoolBV True
{-
    do
    let bτ = mpcValType v̂
    party   ← getParty
    bristol ← cktToBristol ckt
    let cktPath = concat [bristolDir,ppshow party,".txt"]
    io $ fwrite cktPath bristol
    revealed ← runEMP "" party ""
    return $ BoolBV True
    where cktToBristol = return ∘ printBCktVal *∘ generateBristol
          runEMP configPath party input = map Text.pack $ io $ Process.readProcess emp [ Text.unpack configPath, Text.unpack $ show𝕊 party ] $ Text.unpack input
          emp = Text.unpack "emp-backend"
          bristolDir   = "bristol-circuits/" -}

toBristol ∷ (Monad m, MonadIO m) ⇒ 𝐿 PrinVal → MPCVal 'YaoNP → m (𝕊 ∧ (𝐿 𝔹) ∧ ℕ)
toBristol ps v = do
  ((_ :* (BOut input inputOrder gateOrder _midCount gates)) :* (outputWires :* outputSizes)) ← mapSnd split ^$ io $ runRWST null null $ unBM $ addZero ≫ (brisMPCVal v)
  
  io $ out "\n\nGates:\n"
  io $ shout gates
  
  io $ out "\n\nInput:\n"
  pptraceM input
 
  io $ out "\n\nInput Order:\n"
  pptraceM inputOrder
  
  io $ out "\n\nInput Order':\n"
  let inputOrder' = concat $ map
        (\p → case inputOrder ⋕? p of
            Some l → l
            None → null
        ) ps
  pptraceM inputOrder'
  
  io $ out "\n\nGate Order:\n"
  pptraceM gateOrder
  
  io $ out "\n\nOrder:\n"
  let order = inputOrder' ⧺ gateOrder
  pptraceM order

  io $ out "\n\nOutput Order:\n"
  let outputOrder = map (\w → find𝐿 (\(w' :* _) → w == w') order) outputWires
  pptraceM outputOrder

  io $ out "\n\nOutput Order':"
  let outputOrder' :* gates' = fold (null :* gates)
        (\(w :* s) (oo :* gs) → case (w :* s) ∈ pow inputOrder' of
            True →
              let w' = w + 1000000
              in (oo ⧺ single (w' :* s)) :* (gs ⧺ directGates w w' s)
            False → (oo ⧺ single (w :* s)):* gs
        ) outputOrder
  pptraceM outputOrder'

  io $ out "\n\nGate counts:\n"
  io $ shout $ count @ℕ gates
  io $ out " -> "
  io $ shout $ count @ℕ gates'
  
  io $ out "\n\nOrder':\n"
  let order' = list $ (filter (\o → not $ fst o ∈ pow (map fst outputOrder')) order)
  pptraceM order'

  io $ out "\n\nInput Sizes:\n"
  let inputSizes = map
        (\p → case inputOrder ⋕? p of
            Some s → sum $ map snd s
            None → null
        ) ps
  pptraceM inputSizes

  io $ out "\n\nOutput Size:\n"
  pptraceM outputSizes
  
  io $ out "\n\nReverse Wire Map:\n"
  let rwm = makeReverseWireMap order' outputOrder' (sum inputSizes) (count gates')
  pptraceM rwm
  
  let bristol = printBristol rwm inputSizes (sum outputSizes) gates'
  return $ bristol :* input :* (sum outputSizes)

brisMPCVal ∷ MPCVal 'YaoNP → BM (𝐿 (Wire ∧ ℕ))
brisMPCVal = \case
  DefaultMV → error "Found DefaultMV when compiling bristol"
  BulMV → error "Found BulMV when compiling brisol"
  BaseMV ckt → single ^$ brisCkt ckt
  PairMV v1 v2 → concat ^$ mapM brisMPCVal $ frhs [v1, v2]
  SumMV ckt v1 v2 → do
    g ← brisCkt ckt
    --content ← concat ^$ mapM brisMPCVal $ frhs [v1, v2]
    --return $ g :& content
    --To implement, need to mux on g and pad for max length.
    --Either need to add logical wires or map current outputs to mid first.
    error "Revealing SumMV not implemented"
  NilMV → undefined
  ConsMV v1 v2 → undefined

bitsToVal ∷ (Val → ValP) → Type → 𝐿 𝔹 → Val
bitsToVal f t bits = case t of
  BaseT bt → BaseV $ case bt of
    𝔹T → BoolBV $ get𝐿 0 bits
    ℕT pr → NatBV pr $ nat $ unBitBlast @ℕ64 bits
    ℤT pr → IntBV pr $ int $ unBitBlast @ℤ64 bits
    𝔽T pr → FltBV pr $ coerce_UNSAFE $ unBitBlast @ℕ64 bits
  t1 :+: t2 →
    let b :& bits' = bits
    in case b of
      True → LV $ f $ bitsToVal f t1 $ list $ firstN (getBitLengthType t1) bits'
      False → RV $ f $ bitsToVal f t2 $ list $ firstN (getBitLengthType t2) bits'
