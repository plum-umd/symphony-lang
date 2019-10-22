{-# language LambdaCase #-}
{-# language FlexibleContexts #-}
module Netlist where

import           PCL hiding (Env)

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.RWS
import           Control.Monad.Reader
import           Control.Monad.Writer
import           Data.Bits (xor)
import           Data.Map (Map)
import qualified Data.Map as Map

type Netlist = [Gate]

type Wire = Int

data Gate
  = AndGate Wire Wire Wire
  | XorGate Wire Wire Wire
  | InvGate Wire Wire
  | Input Wire
  | Output Wire
  deriving (Show, Read, Eq, Ord)

type Env = Map Var Value

data Value
  = VWire Wire
  | VPair Value Value
  | VClosure Env Var Term
  | VXor
  | VAnd
  | VTrue
  | VFalse
  | VUnit
  deriving (Show, Read, Eq, Ord)

compile :: Term -> Maybe Netlist
compile (Lam (x, ty) t) =
  snd <$> execRWST (do
    vInp <- input ty
    vOut <- local (Map.insert x vInp) (eval t)
    output vOut) Map.empty 0
  where
    input Unit = pure VUnit
    input Boolean = do
      w <- allocWire
      tell [Input w]
      pure (VWire w)
    input (Prod ty0 ty1) = VPair <$> input ty0 <*> input ty1

    output (VWire w) = tell [Output w]
    output (VPair v0 v1) = output v0 >> output v1
    output VUnit = pure ()
    output _ = throwError ()

allocWire :: RWST Env Netlist Wire Maybe Int
allocWire = id <<+= 1

eval :: Term -> RWST Env Netlist Wire Maybe Value
eval = \case
  App t0 t1 -> join (apply <$> eval t0 <*> eval t1)
  Let x t0 t1 -> do
    v0 <- eval t0
    local (Map.insert x v0) (eval t1)
  Lam (x, _) t -> do
    e <- ask
    pure (VClosure e x t)
  Fix d (x, ty@(Arrow inp out)) t -> do
    e <- ask
    let vF = if d <= 0
              then VClosure e "" (manyFalse out)
              else VClosure e "RESERVED" (App (Fix (d-1) (x, ty) t) "RESERVED")
    local (Map.insert x vF) (eval t)
  Var x -> maybe (throwError ()) pure =<< asks (Map.lookup x)
  Pair t0 t1 -> VPair <$> eval t0 <*> eval t1
  Fst t -> do VPair v0 _ <- eval t ; pure v0
  Snd t -> do VPair _ v1 <- eval t ; pure v1
  T -> pure VTrue
  F -> pure VFalse
  Xor -> pure VXor
  And -> pure VAnd
  If cond t0 t1 -> do
    VWire vcond <- eval cond
    join (mux vcond <$> eval t0 <*> eval t1)
  t -> pure VUnit
  where
    mux :: Wire -> Value -> Value -> RWST Env Netlist Wire Maybe Value
    mux cond (VPair v0 v0') (VPair v1 v1') =
      VPair <$> mux cond v0 v1 <*> mux cond v0' v1'
    mux _ VUnit VUnit = pure VUnit
    mux cond v0 v1 = do
      [xorOut, andOut, out] <- replicateM 3 allocWire
      xo <- vxor v0 v1
      ao <- vand (VWire cond) xo
      vxor v1 ao

apply :: Value -> Value -> RWST Env Netlist Wire Maybe Value
apply v0 v1 = case v0 of
  VXor -> let VPair v0' v1' = v1 in vxor v0' v1'
  VAnd -> let VPair v0' v1' = v1 in vand v0' v1'
  VClosure e x t ->
    local (const (Map.insert x v1 e)) (eval t)
  _ -> throwError ()

vxor :: Value -> Value -> RWST Env Netlist Wire Maybe Value
vxor VTrue v = vinv v
vxor v VTrue = vinv v
vxor VFalse v = pure v
vxor v VFalse = pure v
vxor (VWire w0) (VWire w1) = do
  w2 <- allocWire
  tell [XorGate w0 w1 w2]
  pure (VWire w2)
vxor v0 v1 = error (show v0 ++ "\n" ++ show v1)

vinv :: Value -> RWST Env Netlist Wire Maybe Value
vinv VTrue = pure VFalse
vinv VFalse = pure VTrue
vinv (VWire w0) = do
  w1 <- allocWire
  tell [InvGate w0 w1]
  pure (VWire w1)
vinv _ = throwError ()

vand :: Value -> Value -> RWST Env Netlist Wire Maybe Value
vand VTrue v = pure v
vand v VTrue = pure v
vand VFalse _ = pure VFalse
vand _ VFalse = pure VFalse
vand (VWire w0) (VWire w1) = do
  w2 <- allocWire
  tell [AndGate w0 w1 w2]
  pure (VWire w2)
vand _ _ = throwError ()

manyFalse :: Type -> Term
manyFalse Boolean = F
manyFalse (Prod ty0 ty1) = Pair (manyFalse ty0) (manyFalse ty1)
manyFalse Unit = One

run :: Netlist -> [Bool] -> [Bool]
run gates inps = snd $ execRWS (mapM go gates) inps Map.empty
  where
    go = \case
      AndGate w0 w1 w2 -> do
        b0 <- gets (Map.! w0)
        b1 <- gets (Map.! w1)
        id . at w2 .= Just (b0 && b1)
      XorGate w0 w1 w2 -> do
        b0 <- gets (Map.! w0)
        b1 <- gets (Map.! w1)
        id . at w2 .= Just (b0 `xor` b1)
      InvGate w0 w1 -> do
        b <- gets (Map.! w0)
        id . at w1 .= Just (not b)
      Input w -> do
        b <- asks (!! w)
        id . at w .= Just b
      Output w -> do
        b <- gets (Map.! w)
        tell [b]
