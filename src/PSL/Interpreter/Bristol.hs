module PSL.Interpreter.Bristol where

import UVMHS
import AddToUVMHS

import PSL.Syntax
import PSL.Interpreter.Types

import PSL.Interpreter.Circuits

data BCktVal =
    CompBCV BCir (𝐿 ℕ64)
  | InputBCV ℕ64
  deriving (Eq,Ord,Show)

data BCir = BCir
  { bcInputs ∷ 𝐿 ℕ
  , bcOutputs ∷ 𝐿 ℕ
  , bcGates ∷ 𝐿 BGate
  } deriving (Eq,Ord,Show)

data BGate =
    XorBG BWire BWire BWire
  | AndBG BWire BWire BWire
  | InvBG BWire BWire
  | NotBG BWire BWire
  | EqBG BWire BWire
  | EqwBG BWire BWire
  deriving (Eq,Ord,Show)

data BWire =
    InputBW ℕ ℕ
  | OutputBW ℕ ℕ
  | MidBW ℕ
  | ConstBW ℕ
  deriving (Eq,Ord,Show)

type WireMap = 𝐿 (ℕ ∧ (ℕ → BWire))

type RWireMap = (𝐿 ℕ) ∧ ℕ ∧ (𝐿 ℕ)

bristolFrMPCVal ∷ (Monad m) ⇒ MPCVal 'YaoNP → m BCir
bristolFrMPCVal v̂ = undefined

generateBristol ∷ Ckt → IM BCktVal
generateBristol ckt@(Ckt ins gates out) = case gates ⋕! out of
    BaseG bv → case bv of
      BoolBV b → return $ CompBCV (boolToCir b) null
      NatBV _ n → return $ CompBCV (natToCir $ 𝕟64 n) null
    PrimG op ws → do
      let outT = cktType ckt
      cs ← mapM (generateBristol ∘ Ckt ins gates) ws
      oc ← case op :* outT of
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
        NotO :* 𝔹T → return $ invCir $ getBitLength ckt
        CondO :* _ → return $ muxCir $ getBitLength ckt
        EqO :* _ →
          let w :& _ = ws
          in return $ eqCir $ getBitLength $ Ckt ins gates w
      return $ plugInputs (CompBCV oc null) cs

getBitLength ∷ Ckt → ℕ
getBitLength ckt = case wt of
  𝔹T → 1
  ℕT _ → 64 -- precision ignored
  ℤT _ → 64
  𝔽T _ → undefined
  where wt = cktType ckt

invCir ∷ ℕ → BCir
invCir bl = BCir (single bl) (single bl) $ mapOn (frhs [0..(bl - 1)]) $ \i → InvBG (InputBW 0 i) (OutputBW 0 i)

muxCir ∷ ℕ → BCir
muxCir bl =
  let ins = frhs [1,bl,bl]
      ots = single bl
      g = InvBG (InputBW 0 0) (MidBW 0)
      ands1 = fold null (\i acc → AndBG (InputBW 0 0) (InputBW 1 i) (MidBW $ 1 + i) :& acc) $ frhs [0..(bl - 1)]
      ands2 = fold null (\i acc → AndBG (MidBW 0) (InputBW 2 i) (MidBW $ 1 + bl + i) :& acc) $ frhs [0..(bl - 1)]
      xors = fold null (\i acc → XorBG (MidBW $ 1 + i) (MidBW $ 1 + bl + i) (OutputBW 0 i) :& acc) $ frhs [0..(bl - 1)]
  in BCir ins ots $ g :& ands1 ⧺ ands2 ⧺ xors

eqCir ∷ ℕ → BCir
eqCir 0 = undefined
eqCir 1 = BCir (frhs [1,1]) (single 1) $ frhs [XorBG (InputBW 0 0) (InputBW 1 0) (MidBW 0), InvBG (MidBW 0) (OutputBW 0 0)]
eqCir 2 = undefined
eqCir bl =
  let ins = frhs [bl,bl]
      ots = single 1
      xors = fold null (\i acc → XorBG (InputBW 0 i) (InputBW 1 i) (MidBW i) :& acc) $ frhs [0..(bl - 1)]
      invs = fold null (\i acc → InvBG (MidBW i) (MidBW $ i + bl) :& acc) $ frhs [0..(bl - 1)]
      fand = AndBG (MidBW bl) (MidBW $ bl + 1) (MidBW $ bl + bl)
      ands = fold null (\i acc → acc ⧺ (single $ AndBG (MidBW $ bl + bl + i) (MidBW $ 1 + i + bl) (MidBW $ 1 + bl + bl + i))) $ frhs [0..(bl - 3)]
      land = AndBG (MidBW $ bl + bl - 1) (MidBW $ bl + bl + bl - 2) (OutputBW 0 0)
  in BCir ins ots $ xors ⧺ invs ⧺ single fand ⧺ ands ⧺ single land

boolToCir ∷ 𝔹 → BCir
boolToCir = \case
  True → BCir null (single 1) (single $ EqBG (ConstBW 1) (OutputBW 0 0))
  False → BCir null (single 1) (single $ EqBG (ConstBW 0) (OutputBW 0 0))

natToCir ∷ ℕ64 → BCir
natToCir n =
  let gates = fold null (\i acc → EqBG (ConstBW 0) (OutputBW 0 $ 63 - i) :& acc) $ frhs [0..63]
--  let gates = fold null (\i acc → EqBG (ConstBW $ nat $ bget (𝕟64 i) n) (OutputBW 0 $ 63 - i) :& acc) $ frhs [0..63]
  in BCir null (single 64) gates

plugInputs ∷ BCktVal → 𝐿 BCktVal → BCktVal
plugInputs cv@(CompBCV c@(BCir ins ots gates) wns) = \case
  icv :& icvs → case icv of
    InputBCV i → plugInputs (CompBCV c $ wns ⧺ single i) icvs
    CompBCV (BCir ins' (out :& Nil) gates') wns' →
      let ins'' = ins' ⧺ (list $ lastN (count ins - 1) ins)
          offset2 = count gates'
          offset1 = offset2 - out
          numWns = count wns
          gates'' = map (mapGate (firstOutToMid offset1 ∘ bumpInput numWns)) gates'
            ⧺ map (mapGate (inputToMid 0 offset1 ∘ nudgeMid offset2)) gates
          wns'' = wns ⧺ wns'
          cv' = CompBCV (BCir ins'' ots gates'') wns''
      in plugInputs cv' icvs
  Nil → cv

removeDuplicateInputs ∷ BCktVal → BCktVal
removeDuplicateInputs = \case
  InputBCV n → InputBCV n
  CompBCV (BCir ins ots gates) wns →
    undefined

renameInput ∷ ℕ → ℕ → (𝐿 ℕ) ∧ (𝐿 ℕ64) ∧ (𝐿 BGate) → (𝐿 ℕ) ∧ (𝐿 ℕ64) ∧ (𝐿 BGate)
renameInput old new (ins :* wns :* gates) =
  let ins' = undefined
      wns' = undefined
      gates' = undefined
  in undefined

nudgeMid ∷ ℕ → BWire → BWire
nudgeMid offset = \case
  MidBW n → MidBW $ n + offset
  w → w

firstOutToMid ∷ ℕ → BWire → BWire
firstOutToMid offset = \case
  OutputBW 0 n → MidBW $ n + offset
  w → w

inputToMid ∷ ℕ → ℕ → BWire → BWire
inputToMid old offset = \case
  InputBW n o | n == old → MidBW $ o + offset
  w → w

bumpInput ∷ ℕ → BWire → BWire
bumpInput dist = \case
  InputBW n o → InputBW (n + dist) o
  w → w

renameInputWire ∷ ℕ → ℕ → BWire → BWire
renameInputWire old new = \case
  InputBW n o | n == old → InputBW new o
  w → w

mapGate ∷ (BWire → BWire) → BGate → BGate
mapGate f = \case
  XorBG w1 w2 w3 → XorBG (f w1) (f w2) (f w3)
  AndBG w1 w2 w3 → AndBG (f w1) (f w2) (f w3)
  InvBG w1 w2 → InvBG (f w1) (f w2)
  NotBG w1 w2 → NotBG (f w1) (f w2)
  EqBG w1 w2 → EqBG (f w1) (f w2)
  EqwBG w1 w2 → EqwBG (f w1) (f w2)

-- Reading

testB ∷ IO ()
testB = do
  c ← parseCircuitFile "bristol/adder64.txt"
  shout c

parseCircuitFile ∷ 𝕊 → IO BCir
parseCircuitFile fileName = parseCircuit ^$ fread fileName

parseCircuit ∷ 𝕊 → BCir
parseCircuit contents =
  let contents' = list $ splitOn𝕊 "\n" contents
  in case contents' of
       sizes :& inputs :& outputs :& _ :& gates →
         let _ :& wireCount :& _ = list $ splitOn𝕊 " " sizes
             _ :& inputs' = list $ filter (not ∘ isEmpty) $ splitOn𝕊 " " inputs
             _ :& outputs' = list $ filter (not ∘ isEmpty) $ splitOn𝕊 " " outputs
             inputs'' = map read𝕊 inputs'
             outputs'' = map read𝕊 outputs'
             wm = makeWireMap inputs'' outputs'' $ read𝕊 wireCount
             gates' = list $ map (parseGate wm) $ filter (not ∘ isEmpty) gates
         in BCir inputs'' outputs'' gates'
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

makeWireMap ∷ 𝐿 ℕ → 𝐿 ℕ → ℕ → WireMap
makeWireMap is os s =
  let is' = map (\(i :* n) → n :* InputBW i) $ withIndex is
      os' = map (\(i :* n) → n :* OutputBW i) $ withIndex os
      mid = (s - sum is - sum os) :* MidBW
  in list $ is' ⧺ single mid ⧺ os'

-- Writing

printBCktVal ∷ BCktVal → 𝕊
printBCktVal (CompBCV bcir _) = printBCir bcir

printBCir ∷ BCir → 𝕊
printBCir bc@(BCir ins ots gates) =
  let rwm = makeReverseWireMap bc
      wgs = show𝕊 (count @ℕ gates) ⧺ " " ⧺ show𝕊 (count @ℕ gates + sum ins)
      ins' = fold (show𝕊 $ count @ℕ ins) (\i acc → acc ⧺ " " ⧺ show𝕊 i) ins
      ots' = fold (show𝕊 $ count @ℕ ots) (\o acc → acc ⧺ " " ⧺ show𝕊 o) ots
      gates' = concat $ map (printBGateLn rwm) gates
  in wgs ⧺ "\n" ⧺ ins' ⧺ "\n" ⧺ ots' ⧺ "\n\n" ⧺ gates'

printBGateLn ∷ RWireMap → BGate → 𝕊
printBGateLn rwm = \case
  XorBG w1 w2 w3 → "2 1 " ⧺ printBWire rwm w1 ⧺ " " ⧺ printBWire rwm w2 ⧺ " " ⧺ printBWire rwm w3 ⧺ " XOR\n"
  AndBG w1 w2 w3 → "2 1 " ⧺ printBWire rwm w1 ⧺ " " ⧺ printBWire rwm w2 ⧺ " " ⧺ printBWire rwm w3 ⧺ " AND\n"
  InvBG w1 w2 → "1 1 " ⧺ printBWire rwm w1 ⧺ " " ⧺ printBWire rwm w2 ⧺ " INV\n"
  NotBG w1 w2 → "1 1 " ⧺ printBWire rwm w1 ⧺ " " ⧺ printBWire rwm w2 ⧺ " NOT\n"
  EqBG w1 w2 → "1 1 " ⧺ printBWire rwm w1 ⧺ " " ⧺ printBWire rwm w2 ⧺ " EQ\n"
  EqwBG w1 w2 → "1 1 " ⧺ printBWire rwm w1 ⧺ " " ⧺ printBWire rwm w2 ⧺ " EQW\n"

printBWire ∷ RWireMap → BWire → 𝕊
printBWire (ins :* mid :* ots) = show𝕊 ∘ \case
  InputBW n o → lookup𝐿 n ins + o
  MidBW o → mid + o
  OutputBW n o → lookup𝐿 n ots + o
  ConstBW n → n

lookup𝐿 ∷ ℕ → 𝐿 a → a
lookup𝐿 0 (x :& _) = x
lookup𝐿 n (_ :& xs) = lookup𝐿 (n - 1) xs
lookup𝐿 _ _ = error "bad"

makeReverseWireMap ∷ BCir → RWireMap
makeReverseWireMap (BCir ins ots gates) =
  let ins' = list $ reverse $ fold (single 0) (\i (l :& acc) → (i + l) :& l :& acc) $ firstN (count ins - 1) ins
      mid = sum ins
      ots' = list $ reverse $ fold (single $ mid + (count gates - sum ots)) (\i (l :& acc) → (i + l) :& l :& acc) $ firstN (count ots - 1) ots
  in ins' :* mid :* ots'
