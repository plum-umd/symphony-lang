{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language ConstraintKinds #-}
module PCL where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.Map (Map)
import qualified Data.Map as Map

import           Data.String

type Var = String
-- maximum recursive depth
type Depth = Int

type Binding = (Var, Type)
type FBinding = (Var, FType)

data Term
  = App Term Term
  | Let Var Term Term
  | Lam Binding Term
  | Fix Depth FBinding Term
  | Var Var
  | Pair Term Term
  | Fst Term
  | Snd Term
  | T
  | F
  | Xor
  | And
  | If Term Term Term
  | One
  deriving (Show, Read, Eq, Ord)

instance IsString Term where
  fromString = Var

data Type = Boolean | Prod Type Type | Unit
  deriving (Show, Read, Eq, Ord)

data FType = Arrow Type Type
  deriving (Show, Read, Eq, Ord)

type RecDef = (Int, Var, FType)

type Env = Map Var (Either Type FType)

data TypeError
  = TypeMismatch Type Type
  | FTypeMismatch FType FType
  | UnexpectedType Var Type
  | UnexpectedFType Var FType
  | UndefinedVar Var
  | NotProd Term Type
  | NotBoolean Term Type
  | DoesNotHaveType Term
  | DoesNotHaveFType Term
  deriving (Show, Read, Eq, Ord)

type Judge m =
  ( MonadReader (Map Var (Either Type FType)) m
  , MonadError TypeError m
  )

typeCheck :: Term -> Either TypeError FType
typeCheck t = runReaderT (judgeF t) Map.empty

judge :: Judge m => Term -> m Type
judge = \case
  App t0 t1 -> do
    Arrow ty0 ty1 <- judgeF t0
    ty0' <- judge t1
    ensureMatch ty0 ty0'
    pure ty1
  Let v t0 t1 -> do
    ty0 <- judge t0
    local (Map.insert v (Left ty0)) (judge t1)
  Var v ->
    asks (Map.lookup v) >>= \case
      Nothing -> throwError (UndefinedVar v)
      Just (Right ft) -> throwError (UnexpectedFType v ft)
      Just (Left t) -> pure t
  Pair t0 t1 -> Prod <$> judge t0 <*> judge t1
  Fst t ->
    judge t >>= \case
      Prod ty0 _ -> pure ty0
      ty -> throwError (NotProd t ty)
  Snd t ->
    judge t >>= \case
      Prod _ ty1 -> pure ty1
      ty -> throwError (NotProd t ty)
  T -> pure Boolean
  F -> pure Boolean
  If cond t0 t1 ->
    judge cond >>= \case
      Boolean -> do
        ty0 <- judge t0
        ty1 <- judge t1
        ensureMatch ty0 ty1
        pure ty0
      ty -> throwError (NotBoolean cond ty)
  One -> pure Unit
  t -> throwError (DoesNotHaveType t)
  where
    ensureMatch ty ty' =
      when (ty /= ty') (throwError (TypeMismatch ty ty'))

judgeF :: Judge m => Term -> m FType
judgeF = \case
  Lam (x, ty0) t -> Arrow ty0 <$> local (Map.insert x (Left ty0)) (judge t)
  Fix d (x, ty) t -> do
    ty' <- local (Map.insert x (Right ty)) (judgeF t)
    ensureMatch ty ty'
    pure ty

  Var v ->
    asks (Map.lookup v) >>= \case
      Nothing -> throwError (UndefinedVar v)
      Just (Left t) -> throwError (UnexpectedType v t)
      Just (Right ft) -> pure ft
  Xor -> pure (Prod Boolean Boolean `Arrow` Boolean)
  And -> pure (Prod Boolean Boolean `Arrow` Boolean)
  t -> throwError (DoesNotHaveFType t)
  where
    ensureMatch ty ty' =
      when (ty /= ty') (throwError (FTypeMismatch ty ty'))
