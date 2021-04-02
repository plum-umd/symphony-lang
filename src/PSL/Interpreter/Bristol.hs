module PSL.Interpreter.Bristol where

import UVMHS
import AddToUVMHS

import PSL.Syntax
import PSL.Interpreter.Types

import PSL.Interpreter.Circuits

-- Data Structures

data BGate =
    XorBG BWire BWire BWire
  | AndBG BWire BWire BWire
  | InvBG BWire BWire
  | NotBG BWire BWire
  | EqBG BWire BWire
  | EqwBG BWire BWire
  deriving (Eq,Ord,Show)

data BWire =
    TempBW ℕ ℕ
  | PlugBW Wire ℕ
  | MidBW ℕ
  | ZeroBW
  | ConstBW 𝔹
  deriving (Eq,Ord,Show)

-- Offsets for reading in bristol
type WireMap = 𝐿 (ℕ ∧ (ℕ → BWire))

-- Offsets for writing bristol
type RWireMap = (Wire ⇰ ℕ) ∧ ℕ


-- RWST

data BCxt = BCxt
  { bcGates ∷ Wire ⇰ Gate
  } deriving (Eq,Ord,Show)
makeLenses ''BCxt

data BState = BState
  { bsDone ∷ 𝑃 Wire
  }
makeLenses ''BState

instance Null BState where
  null = BState null

data BOut = BOut
  { boMidCount ∷ ℕ
  , boCir ∷ 𝐿 BGate
  } deriving (Eq,Ord,Show)
makeLenses ''BOut

instance Null BOut where
  null = BOut 0 null

instance Append BOut where
  (⧺) (BOut oldCount oldGates) (BOut newCount newGates) = BOut (oldCount + newCount) $ oldGates ⧺ map (mapGate $ nudgeMid oldCount) newGates

instance Monoid BOut

newtype BM a = BM { unBM ∷ RWST BCxt BOut BState IO a}
  deriving
  ( Functor,Return,Bind,Monad
  , MonadReader BCxt
  , MonadWriter BOut
  , MonadState BState
  , MonadIO
  )

--Bristol

-- Current party → All parties in order → the circuit
--   → Bristol File ∧ Current party's concatenated input
toBristol ∷ 𝐿 PrinVal → Ckt → IM (𝕊 ∧ (𝐿 𝔹))
toBristol ps ckt = do
  BOut _ gates ← brisCkt ckt
  io $ out "\n\nGates:\n"
  io $ shout gates
  let input = generateInput ckt
  io $ out "\n\nInput:\n"
  io $ shout input
  let inputOrder = getPrinInputOrder ckt
  io $ out "\n\nInput Order:\n"
  io $ shout inputOrder
  let inputOrder' = concat $ map (\p → inputOrder ⋕! p) ps
  io $ out "\n\nInput Order':\n"
  io $ shout inputOrder
  let gateOrder = getGateInputOrder ckt
  io $ out "\n\nGate Order:\n"
  io $ shout gateOrder
  let order = inputOrder' ⧺ gateOrder
  io $ out "\n\nOrder:\n"
  io $ shout order
  let order' = list $ (filter (\o → not $ fst o == outC ckt) order)
  io $ out "\n\nOrder':\n"
  io $ shout order'
  let outputOrder :& _ = list $ (filter (\o → fst o == outC ckt) order)
  io $ out "\n\nOutput Order:\n"
  io $ shout outputOrder
  let inputSizes = map (\p → sum $ map snd $ inputOrder ⋕! p) ps
  io $ out "\n\nInput Sizes:\n"
  io $ shout inputSizes
  let outputSize = getBitLength $ cktType ckt
  io $ out "\n\nOutput Size:\n"
  io $ shout outputSize
  let rwm = makeReverseWireMap order' outputOrder (sum inputSizes) (count gates)
  io $ out "\n\nReverse Wire Map:\n"
  io $ shout rwm
  let bristol = printBristol rwm inputSizes outputSize gates
  return $ bristol :* input

brisCkt ∷ Ckt → IM BOut
brisCkt (Ckt gates ot) = snd ∘ fst ^$ io $ runRWST (BCxt gates) null $ unBM $ addZero ≫ (generateGates ot)

addZero ∷ BM ()
addZero = pushGates null 1 $ single $ XorBG (ConstBW False) (ConstBW False) ZeroBW

generateGates ∷ Wire → BM ()
generateGates lw = do
  done ← isDone lw
  case done of
    True → skip
    False → do
      gate ← lookupGate lw
      case gate of
        BaseG bv → do
          let gates = case bv of
                BoolBV b → bitsToCir (𝕟64 1) b
                NatBV _ n → bitsToCir (𝕟64 64) $ 𝕟64 n
                -- TODO: How to get the bits from an integer?
                IntBV _ i → bitsToCir (𝕟64 64) $ 𝕟64 42 --elim𝑂 (error "Int too big") id $ intO64 i
                -- TODO: How to get the bits from a float?
                FltBV _ _f → undefined
          pushGates (single lw) 0 gates
        InputG _ _ → markDone lw
        PrimG op ws → do
          mapM generateGates ws
          t ← getWireType lw
          gates ← case op :* t of
            PlusO :* ℤT _ → io $ parseCircuitFile "bristol/adder64.txt"
            PlusO :* 𝔽T  _→ io $ parseCircuitFile "bristol/FP-add.txt"
            MinusO :* ℤT _ → io $ parseCircuitFile "bristol/sub64.txt"
            TimesO :* ℤT _ → io $ parseCircuitFile "bristol/mult64.txt"
            TimesO :* 𝔽T _ → io $ parseCircuitFile "bristol/FP-mul.txt"
            DivO :* ℤT _ → io $ parseCircuitFile "bristol/divide64.txt"
            DivO :* 𝔽T _ → io $ parseCircuitFile "bristol/FP-div.txt"
            SqrtO :* 𝔽T _ → io $ parseCircuitFile "bristol/FP-sqrt.txt"
            LTO :* 𝔽T _ → io $ parseCircuitFile "bristol/FP-lt.txt"
            FltO _ :* 𝔽T _ → io $ parseCircuitFile "bristol/FP-i2f.txt"
            IntO _ :* ℤT _ → io $ parseCircuitFile "bristol/FP-f2i.txt"
            CeilO _ :* 𝔽T _ → io $ parseCircuitFile "bristol/FP-ceil.txt"
            OrO :* 𝔹T → return orCir
            AndO :* 𝔹T → return andCir
            NotO :* 𝔹T → return $ invCir $ getBitLength t
            CondO :* _ → return $ muxCir $ getBitLength t
            EqO :* _ → return $ eqCir $ getBitLength t
          pushGates (ws ⧺ single lw) (count gates - getBitLength t) gates
      markDone lw

generateInput ∷ Ckt → 𝐿 𝔹
generateInput (Ckt gates _) = concat $ map
  (\case
      _ :* (InputG _ (AvailableI bv)) → case bv of
        BoolBV b → bitBlast (𝕟64 1) b
        NatBV _ n → bitBlast (𝕟64 64) $ 𝕟64 n
        -- TODO: How to get the bits from an integer?
        IntBV _ i → bitBlast (𝕟64 64) $ 𝕟64 42 --elim𝑂 (error "Int too big") id $ intO64 i
        -- TODO: How to get the bits from a float?
        FltBV _ _f → undefined
      _ → null
  ) $ iter gates

getPrinInputOrder ∷ Ckt → PrinVal ⇰ 𝐿 (Wire ∧ ℕ)
getPrinInputOrder (Ckt gates _) = fold null
  (\(w :* g) acc →
     let m = case g of
           (InputG p (AvailableI bv)) → Some (p ↦ single (w :* (getBitLength $ typeOfBaseVal bv)))
           (InputG p (UnavailableI bt)) → Some (p ↦ single (w :* (getBitLength bt)))
           _ → None
     in case m of
       Some il → unionWith (⧺) acc il
       None → acc
  ) $ iter gates

getGateInputOrder ∷ Ckt → 𝐿 (Wire ∧ ℕ)
getGateInputOrder ckt@(Ckt gates _) = concat $ map
  (\case
      _ :* (InputG _ _) → null
      w :* _ → single $ w :* (getBitLength $ wireType ckt w)
  ) $ iter gates

-- Util

isDone ∷ Wire → BM 𝔹
isDone w = (w ∈) ^$ getL bsDoneL

markDone ∷ Wire → BM ()
markDone lw = do
  modifyL bsDoneL (∪ (single lw))

lookupGate ∷ Wire → BM Gate
lookupGate wire = (⋕! wire) ^$ askL bcGatesL

getWireType ∷ Wire → BM BaseType
getWireType lw = do
  gates ← askL bcGatesL
  return $ cktType $ Ckt gates lw

getBitLength ∷ BaseType → ℕ
getBitLength = \case
  𝔹T → 1
  ℕT _ → 64
  ℤT _ → 64
  𝔽T _ → 64

get𝐿 ∷ ℕ → 𝐿 a → a
get𝐿 0 (x :& _) = x
get𝐿 n (_ :& xs) = get𝐿 (n - 1) xs
get𝐿 _ _ = error "bad"

pushGates ∷ 𝐿 Wire → ℕ → 𝐿 BGate → BM ()
pushGates pws c gates = do
  let f = fold id (\(i :* pw) acc → assignTempWire i pw ∘ acc) $ withIndex pws
  tell $ BOut c $ map (mapGate f) gates

nudgeMid ∷ ℕ → BWire → BWire
nudgeMid offset = \case
  MidBW n → MidBW $ n + offset
  w → w

assignTempWire ∷ ℕ → Wire → BWire → BWire
assignTempWire old new = \case
  TempBW n o | n == old → PlugBW new o
  w → w

mapGate ∷ (BWire → BWire) → BGate → BGate
mapGate f = \case
  XorBG w1 w2 w3 → XorBG (f w1) (f w2) (f w3)
  AndBG w1 w2 w3 → AndBG (f w1) (f w2) (f w3)
  InvBG w1 w2 → InvBG (f w1) (f w2)
  NotBG w1 w2 → NotBG (f w1) (f w2)
  EqBG w1 w2 → EqBG (f w1) (f w2)
  EqwBG w1 w2 → EqwBG (f w1) (f w2)

bitBlast ∷ Bitty a ⇒ Eq a ⇒ ℕ64 → a → 𝐿 𝔹
bitBlast s x = map (\i → bget i x) $ frhs [𝕟64 0..(s - (𝕟64 1))]

-- Circuit Generation

invCir ∷ ℕ → 𝐿 BGate
invCir bl = mapOn (frhs [0..(bl - 1)]) $ \i → InvBG (TempBW 0 i) (TempBW 1 i)

muxCir ∷ ℕ → 𝐿 BGate
muxCir bl =
  let g = InvBG (TempBW 0 0) (MidBW 0)
      ands1 = fold null (\i acc → AndBG (TempBW 0 0) (TempBW 1 i) (MidBW $ 1 + i) :& acc) $ frhs [0..(bl - 1)]
      ands2 = fold null (\i acc → AndBG (MidBW 0) (TempBW 2 i) (MidBW $ 1 + bl + i) :& acc) $ frhs [0..(bl - 1)]
      xors = fold null (\i acc → XorBG (MidBW $ 1 + i) (MidBW $ 1 + bl + i) (TempBW 3 i) :& acc) $ frhs [0..(bl - 1)]
  in g :& ands1 ⧺ ands2 ⧺ xors

eqCir ∷ ℕ → 𝐿 BGate
eqCir 0 = undefined
eqCir 1 = frhs [XorBG (TempBW 0 0) (TempBW 1 0) (MidBW 0), InvBG (MidBW 0) (TempBW 2 0)]
eqCir 2 = undefined
eqCir bl =
  let xors = fold null (\i acc → XorBG (TempBW 0 i) (TempBW 1 i) (MidBW i) :& acc) $ frhs [0..(bl - 1)]
      invs = fold null (\i acc → InvBG (MidBW i) (MidBW $ i + bl) :& acc) $ frhs [0..(bl - 1)]
      fand = AndBG (MidBW bl) (MidBW $ bl + 1) (MidBW $ bl + bl)
      ands = fold null (\i acc → acc ⧺ (single $ AndBG (MidBW $ bl + bl + i) (MidBW $ 1 + i + bl) (MidBW $ 1 + bl + bl + i))) $ frhs [0..(bl - 3)]
      land = AndBG (MidBW $ bl + bl - 1) (MidBW $ bl + bl + bl - 2) (TempBW 2 0)
  in xors ⧺ invs ⧺ single fand ⧺ ands ⧺ single land

andCir ∷ 𝐿 BGate
andCir = single $ AndBG (TempBW 0 0) (TempBW 1 0) (TempBW 2 0)

orCir ∷ 𝐿 BGate
orCir = frhs
  [ InvBG (TempBW 0 0) (MidBW 0)
  , InvBG (TempBW 1 0) (MidBW 1)
  , AndBG (MidBW 0) (MidBW 1) (MidBW 2)
  , InvBG (MidBW 2) (TempBW 2 0)
  ]

bitsToCir ∷ Bitty a ⇒ Eq a ⇒ ℕ64 → a → 𝐿 BGate
bitsToCir s n = list $ map (\(i :* b) →
                                 if b
                                 then InvBG ZeroBW (TempBW 0 i)
                                 else XorBG ZeroBW ZeroBW (TempBW 0 i)
                              ) $ withIndex $ bitBlast s n

---- Reading

parseCircuitFile ∷ 𝕊 → IO (𝐿 BGate)
parseCircuitFile fileName = parseCircuit ^$ fread fileName

parseCircuit ∷ 𝕊 → 𝐿 BGate
parseCircuit contents =
  let contents' = list $ splitOn𝕊 "\n" contents
  in case contents' of
       sizes :& inputs :& outputs :& _ :& gates →
         let _ :& wireCount :& _ = list $ splitOn𝕊 " " sizes
             _ :& inputs' = list $ filter (not ∘ isEmpty) $ splitOn𝕊 " " inputs
             _ :& outputs' = list $ filter (not ∘ isEmpty) $ splitOn𝕊 " " outputs
             inputBitLengths = map read𝕊 inputs'
             outputBitLength :& _ = map read𝕊 outputs'
             wm = makeWireMap inputBitLengths outputBitLength $ read𝕊 wireCount
         in list $ map (parseGate wm) $ filter (not ∘ isEmpty) gates
       _ → error "bad file"

parseGate ∷ WireMap → 𝕊 → BGate
parseGate wm line =
  let _ :& _ :& line' = list $ splitOn𝕊 " " line
  in case line' of
    i1 :& i2 :& o :& "XOR" :& Nil → XorBG (parseWire wm i1) (parseWire wm i2) (parseWire wm o)
    i1 :& i2 :& o :& "AND" :& Nil → AndBG (parseWire wm i1) (parseWire wm i2) (parseWire wm o)
    i :& o :& "INV" :& Nil → InvBG (parseWire wm i) (parseWire wm o)
    i :& o :& "NOT" :& Nil → NotBG (parseWire wm i) (parseWire wm o)
    i :& o :& "EQ" :& Nil → EqBG (ConstBW $ read𝕊 i) (parseWire wm o)
    i :& o :& "EQW" :& Nil → EqwBG (parseWire wm i) (parseWire wm o)
    _ → error "bad file"

parseWire ∷ WireMap → 𝕊 → BWire
parseWire wm n =
  let n' = read𝕊 n
  in lookupWireMap wm n'

lookupWireMap ∷ WireMap → ℕ → BWire
lookupWireMap wm n = case wm of
  (n' :* f) :& _ | n < n' → f n
  (n' :* _) :& wm' → lookupWireMap wm' $ n - n'
  Nil → error "bad"

makeWireMap ∷ 𝐿 ℕ → ℕ → ℕ → WireMap
makeWireMap ibls obl s =
  let ps' = map (\(tw :* bl) → bl :* TempBW tw) $ withIndex ibls
      o = single $ obl :* TempBW (count ibls)
      mid = single $ (s - sum ibls - obl) :* MidBW
  in list $ ps' ⧺ mid ⧺ o

---- Writing

printBristol ∷ RWireMap → 𝐿 ℕ → ℕ → 𝐿 BGate → 𝕊
printBristol rwm ins ot gates =
  let wgs = show𝕊 (count @ℕ gates) ⧺ " " ⧺ show𝕊 (count @ℕ gates + sum ins)
      ins' = fold (show𝕊 $ count @ℕ ins) (\i acc → acc ⧺ " " ⧺ show𝕊 i) ins
      ot' = "1 " ⧺ show𝕊 ot
      gates' = concat $ map (printBGateLn rwm) gates
  in wgs ⧺ "\n" ⧺ ins' ⧺ "\n" ⧺ ot' ⧺ "\n\n" ⧺ gates'

printBGateLn ∷ RWireMap → BGate → 𝕊
printBGateLn rwm = \case
  XorBG w1 w2 w3 → "2 1 " ⧺ printBWire rwm w1 ⧺ " " ⧺ printBWire rwm w2 ⧺ " " ⧺ printBWire rwm w3 ⧺ " XOR\n"
  AndBG w1 w2 w3 → "2 1 " ⧺ printBWire rwm w1 ⧺ " " ⧺ printBWire rwm w2 ⧺ " " ⧺ printBWire rwm w3 ⧺ " AND\n"
  InvBG w1 w2 → "1 1 " ⧺ printBWire rwm w1 ⧺ " " ⧺ printBWire rwm w2 ⧺ " INV\n"
  NotBG w1 w2 → "1 1 " ⧺ printBWire rwm w1 ⧺ " " ⧺ printBWire rwm w2 ⧺ " NOT\n"
  EqBG w1 w2 → "1 1 " ⧺ printBWire rwm w1 ⧺ " " ⧺ printBWire rwm w2 ⧺ " EQ\n"
  EqwBG w1 w2 → "1 1 " ⧺ printBWire rwm w1 ⧺ " " ⧺ printBWire rwm w2 ⧺ " EQW\n"

printBWire ∷ RWireMap → BWire → 𝕊
printBWire (ps :* mid) = show𝕊 ∘ \case
  PlugBW n o → (ps ⋕! n) + o
  MidBW o → mid + o
  ZeroBW → mid
  ConstBW True → 1
  ConstBW False → 0
  TempBW _ _ → error "Bad"

makeReverseWireMap ∷ 𝐿 (Wire ∧ ℕ) → (Wire ∧ ℕ) → ℕ → ℕ → RWireMap
makeReverseWireMap ((w1 :* fbl) :& wbls) (ow :* obl) inputSize gatesLength =
  let ws :* bls = split wbls
      ps = dict𝐼 $ reverse $ fold (single $ w1 :* 0) (\(w :* bl) ((w' :* l) :& acc) → (w :* (bl + l)) :& (w' :* l) :& acc) $ zip ws $ fbl :& bls
      mid = sum $ fbl :& bls
      o = (ow ↦ (inputSize + gatesLength - obl))
  in (ps ⩌ o) :* mid
