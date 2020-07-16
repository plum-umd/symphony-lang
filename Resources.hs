module Resources where

import Prelude

import Data.Set.Strict (Set)
import qualified Data.Set.Strict as Set

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Numeric.Natural

type Set a = [a]

data Prot = 
    YaoP  -- yao
  | BGWP  -- bgw
  | GMWP  -- gmw
  | BGVP  -- bgv
  | SPDZP -- spdz
  | AutoP -- auto
  deriving (Eq,Ord,Show)

data Type =
    BoolT
  | NatT Natural -- Natural = precision
  | IntT         -- Natural = precision
  | FltT         -- assume 64-bit
  deriving (Eq,Ord,Show)

data TypedOp =
    OrO                  -- e || e          types: bool
  | AndO                 -- e && e          types: bool
  | NotO                 -- not e           types: bool
  | PlusO Type           -- e + e           types: nat,int,flt
  | MinusO Type          -- e - e           types: nat*,int,flt (* = underflow?)
  | TimesO Type          -- e * e           types: nat,int,flt
  | ExpO Type            -- exp e           types:
  | DivO Type            -- e / e           types:
  | ModO Type            -- e % e           types:
  | EqO Type             -- e == e          types:
  | LTO Type             -- e < e           types:
  | GTO Type             -- e > e           types:
  | LTEO Type            -- e <= e          types:
  | GTEO Type            -- e >= e          types:
  | CondO Type           -- e ? e >< e      types:
  | AbsO Type            -- abs_val e       types:
  | SqrtO Type           -- sqrt e          types:
  | LogO Type            -- log_base_2 e    types:
  | NatO Natural Type    -- nat#n.n         types:
  | IntO Natural Type    -- int#n.n         types:
  | FltO Natural Type    -- flt#n.n         types:
  | CeilO Natural Type   -- ceil#n.n        types:
  | ShareO (Set PrinVal) Type    -- share  ; the Set PrinVal is the "to" set
  | RevealO (Set PrinVal) Type   -- reveal ; the Set PrinVal is the "to" set
                                 -- (the set of prins in the event is
                                 -- the "from" set)
  deriving (Eq,Ord,Show)
    

type PrinVal = String

data ResEvent = ResEvent
  { resEvZK :: Bool
  , resEvProt :: Prot
  , resEvPrins :: Set PrinVal
  , resEvOp :: TypedOp
  , resEvMd :: Natural
  } deriving (Eq,Ord,Show)

data ResEstimate = ResEstimate
  { resEsComm :: Natural   -- change to polynomial
  , resEsRounds :: Natural -- change to polynomial
  } deriving (Eq,Ord,Show)

interpretEvents :: [(ResEvent, Natural)] -> ResEstimate
interpretEvents = undefined

myTable :: Map Strint Integer
myTable = Map.fromList
  [ ("thing", 1) 
  , ("blah",  2)
  ]

exampleInput :: [(ResEvent, Natural)]
exampleInput = 
  [ (ResEv False Yao (Set.fromList ["A","B"]) (LTEO (IntT 32)) 0, 1) ]



{- 
[package.yaml]:

name: psl
version: 0.1.0.0

library:
  source-dirs: 
    - src
  dependencies:
    - containers

[stack.yaml]:

resolver: lts-14.27
-}
