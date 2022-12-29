module Symphony.Dynamic.Par.Yao ( module Symphony.Dynamic.Par.Yao ) where

import Symphony.Prelude
import qualified Prelude as HS
import qualified Data.Bits as BITS
import Foreign.ForeignPtr (newForeignPtr, withForeignPtr, finalizeForeignPtr, ForeignPtr, FinalizerPtr)
import Foreign.Ptr (Ptr)
import Foreign.C.Types (CSize(..), CBool(..), CUInt(..), CInt(..))
import Foreign.Marshal.Array (withArrayLen, withArray)
import Foreign.Marshal.Utils (toBool, fromBool)
import qualified Data.Text as T

import Symphony.Lang.Syntax

import Symphony.Dynamic.Par.Prg
import Symphony.Dynamic.Par.Channel

import Symphony.Dynamic.Par.Yao.Types as Symphony.Dynamic.Par.Yao

-- Utilities, these should be moved to Prelude

unChans ∷ 𝐿 Channel → [ForeignPtr CChannel]
unChans chans = tohs $ list $ map unChannel $ iter chans

reflectPtr ∷ (a → IO (Ptr b)) → FinalizerPtr b → a → IO (ForeignPtr b)
reflectPtr reflect elim v = newForeignPtr elim *$ reflect v

unaryPtr ∷ (Ptr a → IO (Ptr b)) → FinalizerPtr b → ForeignPtr a → IO (ForeignPtr b)
unaryPtr op elim v =
  withForeignPtr v $ \ v →
  newForeignPtr elim *$ op v

binaryPtr ∷ (Ptr a → Ptr b → IO (Ptr c)) → FinalizerPtr c → ForeignPtr a → ForeignPtr b → IO (ForeignPtr c)
binaryPtr op elim v₁ v₂ =
  withForeignPtr v₁ $ \ v₁ →
  withForeignPtr v₂ $ \ v₂ →
  newForeignPtr elim *$ op v₁ v₂

reifyPtr ∷ (Ptr a → IO b) → ForeignPtr a → IO b
reifyPtr reify v =
  withForeignPtr v $ \ v →
  reify v

--------------------
--- YAO Protocol ---
--------------------

foreign import ccall unsafe "yao_protocol_new" yao_protocol_new ∷ CSize → CAddr → CPort → IO (Ptr CYao)

yaoProtocolNew ∷ (Monad m, MonadIO m) ⇒ PrinVal → (PrinVal ⇰ (Addr ∧ Port)) → m Yao
yaoProtocolNew me chans = io $
  withCString caddr $ \ caddr_ptr →
  Yao ^$ newForeignPtr yao_protocol_drop *$ yao_protocol_new cme caddr_ptr cport
  where cme    = HS.fromIntegral $ fromSome $ idsFr (keys chans) ⋕? me
        caddrs = lazyList𝐼 $ map (T.unpack ∘ fst ∘ snd) $ iter chans
        cports = tohs $ list $ map (HS.fromIntegral ∘ snd ∘ snd) $ iter chans

foreign import ccall unsafe "&yao_protocol_drop" yao_protocol_drop ∷ FinalizerPtr CYao

yaoProtocolDrop ∷ (Monad m, MonadIO m) ⇒ Yao → m ()
yaoProtocolDrop yao = io $ finalizeForeignPtr $ unYao yao

withYao ∷ Yao → (Ptr CYao → IO a) → IO a
withYao yao f = withForeignPtr cyao f
  where cyao = unYao yao

yaoReflect ∷ (Ptr CYao → a → IO (Ptr b)) → FinalizerPtr b → Yao → a → IO (ForeignPtr b)
yaoReflect reflect elim yao v =
  withYao yao $ \ yao →
  reflectPtr (reflect yao) elim v

yaoUnary ∷ (Ptr CYao → Ptr a → IO (Ptr b)) → FinalizerPtr b → Yao → ForeignPtr a → IO (ForeignPtr b)
yaoUnary op elim yao v =
  withYao yao $ \ yao →
  unaryPtr (op yao) elim v

yaoBinary ∷ (Ptr CYao → Ptr a → Ptr b → IO (Ptr c)) → FinalizerPtr c → Yao → ForeignPtr a → ForeignPtr b → IO (ForeignPtr c)
yaoBinary op elim yao v₁ v₂ =
  withYao yao $ \ yao →
  binaryPtr (op yao) elim v₁ v₂

yaoReify ∷ (Ptr CYao → Ptr a → IO b) → Yao → ForeignPtr a → IO b
yaoReify reify yao v =
  withYao yao $ \ yao →
  reifyPtr (reify yao) v

yaoShareSend ∷ (Ptr CPrg → Ptr (Ptr CChannel) → CSize → a → IO ()) → Prg → 𝐿 Channel → a → IO ()
yaoShareSend shareSend prg chans v =
  withForeignPtr (unPrg prg) $ \ prg →
  withForeignPtrs (unChans chans) $ \ chans →
  withArrayLen chans $ \ len buf →
  shareSend prg buf (HS.fromIntegral len) v

yaoShareRecv ∷ (Ptr CChannel → IO a) → Channel → IO a
yaoShareRecv shareRecv chan =
  withForeignPtr (unChannel chan) $ \ chan →
  shareRecv chan

yaoRevealSend ∷ (Ptr CChannel → a → IO ()) → Channel → a → IO ()
yaoRevealSend revealSend chan v =
  withForeignPtr (unChannel chan) $ \ chan →
  revealSend chan v

yaoRevealRecv ∷ (Ptr (Ptr CChannel) → CSize → IO a) → 𝐿 Channel → IO a
yaoRevealRecv revealRecv chans =
  withForeignPtrs (unChans chans) $ \ chans →
  withArrayLen chans $ \ len buf →
  revealRecv buf (HS.fromIntegral len)

----------------
--- YAO Bool ---
----------------

foreign import ccall unsafe "yao_bool_new" yao_bool_new ∷ Ptr CYao → CBool → IO (Ptr CYaoBool)

yaoBoolNew ∷ (Monad m, MonadIO m) ⇒ Yao → 𝔹 → m YaoBool
yaoBoolNew yao share = io $ YaoBool ^$ yaoReflect yao_bool_new yao_bool_drop yao $ fromBool share

foreign import ccall unsafe "yao_bool_constant" yao_bool_constant ∷ Ptr CYao → CBool → IO (Ptr CYaoBool)

yaoBoolConstant ∷ (Monad m, MonadIO m) ⇒ Yao → 𝔹 → m YaoBool
yaoBoolConstant yao value = io $ YaoBool ^$ yaoReflect yao_bool_constant yao_bool_drop yao $ fromBool value

foreign import ccall unsafe "yao_bool_and" yao_bool_and ∷ Ptr CYao → Ptr CYaoBool → Ptr CYaoBool → IO (Ptr CYaoBool)

yaoBoolAnd ∷ (Monad m, MonadIO m) ⇒ Yao → YaoBool → YaoBool → m YaoBool
yaoBoolAnd yao v₁ v₂ = io $ YaoBool ^$ yaoBinary yao_bool_and yao_bool_drop yao (unYaoBool v₁) (unYaoBool v₂)

foreign import ccall unsafe "yao_bool_or" yao_bool_or ∷ Ptr CYao → Ptr CYaoBool → Ptr CYaoBool → IO (Ptr CYaoBool)

yaoBoolOr ∷ (Monad m, MonadIO m) ⇒ Yao → YaoBool → YaoBool → m YaoBool
yaoBoolOr yao v₁ v₂ = io $ YaoBool ^$ yaoBinary yao_bool_or yao_bool_drop yao (unYaoBool v₁) (unYaoBool v₂)

foreign import ccall unsafe "yao_bool_mux" yao_bool_mux ∷ Ptr CYao → Ptr CYaoBool → Ptr CYaoBool → Ptr CYaoBool → IO (Ptr CYaoBool)

yaoBoolMux ∷ (Monad m, MonadIO m) ⇒ Yao → YaoBool → YaoBool → YaoBool → m YaoBool
yaoBoolMux yao v₁ v₂ v₃ = io $ YaoBool ^$
  withYao yao $ \ yao →
  withForeignPtr (unYaoBool v₁) $ \ b₁ →
  withForeignPtr (unYaoBool v₂) $ \ b₂ →
  withForeignPtr (unYaoBool v₃) $ \ b₃ →
  newForeignPtr yao_bool_drop *$ yao_bool_mux yao b₁ b₂ b₃

foreign import ccall unsafe "yao_bool_get" yao_bool_get ∷ Ptr CYao → Ptr CYaoBool → IO CBool

yaoBoolGet ∷ (Monad m, MonadIO m) ⇒ Yao → YaoBool → m 𝔹
yaoBoolGet yao share = io $ toBool ^$ yaoReify yao_bool_get yao (unYaoBool share)

foreign import ccall unsafe "&yao_bool_drop" yao_bool_drop ∷ FinalizerPtr CYaoBool

-- Delegation --

foreign import ccall unsafe "yao_share_send_bool" yao_share_send_bool ∷ Ptr CPrg → Ptr (Ptr CChannel) → CSize → CBool → IO ()

yaoShareSendBool ∷ (Monad m, MonadIO m) ⇒ Prg → 𝐿 Channel → 𝔹 → m ()
yaoShareSendBool prg chans input = io $ yaoShareSend yao_share_send_bool prg chans $ fromBool input

foreign import ccall unsafe "yao_share_recv_bool" yao_share_recv_bool ∷ Ptr CChannel → IO CBool

yaoShareRecvBool ∷ (Monad m, MonadIO m) ⇒ Channel → m 𝔹
yaoShareRecvBool chan = io $ toBool ^$ yaoShareRecv yao_share_recv_bool chan

foreign import ccall unsafe "yao_reveal_send_bool" yao_reveal_send_bool ∷ Ptr CChannel → CBool → IO ()

yaoRevealSendBool ∷ (Monad m, MonadIO m) ⇒ Channel → 𝔹 → m ()
yaoRevealSendBool chan output = io $ yaoRevealSend yao_reveal_send_bool chan $ fromBool output

foreign import ccall unsafe "yao_reveal_recv_bool" yao_reveal_recv_bool ∷ Ptr (Ptr CChannel) → CSize → IO CBool

yaoRevealRecvBool ∷ (Monad m, MonadIO m) ⇒ 𝐿 Channel → m 𝔹
yaoRevealRecvBool chans = io $ toBool ^$ yaoRevealRecv yao_reveal_recv_bool chans

yaoShareRecvYaoBool ∷ (Monad m, MonadIO m) ⇒ Yao → Channel → m YaoBool
yaoShareRecvYaoBool yao chan = do
  b ← yaoShareRecvBool chan
  yaoBoolNew yao b

yaoRevealSendYaoBool ∷ (Monad m, MonadIO m) ⇒ Yao → Channel → YaoBool → m ()
yaoRevealSendYaoBool yao chan share = do
  b ← yaoBoolGet yao share
  yaoRevealSendBool chan b

yaoReshareSendBool ∷ (Monad m, MonadIO m) ⇒ Yao → Prg → 𝐿 Channel → YaoBool → m ()
yaoReshareSendBool yao prg channels share = do
  b ← yaoBoolGet yao share
  yaoShareSendBool prg channels b

yaoReshareRecvYaoBool ∷ (Monad m, MonadIO m) ⇒ Yao → 𝐿 Channel → m YaoBool
yaoReshareRecvYaoBool yao chans = do
  shares ← mapM yaoShareRecvBool chans
  yaoBoolNew yao $ fold False (BITS.xor) shares

----------------------------------
--- YAO Natural (Unsigned Int) ---
----------------------------------

foreign import ccall unsafe "yao_nat32_new" yao_nat32_new ∷ Ptr CYao → CUInt → IO (Ptr CYaoNat)

yaoNatNew ∷ (Monad m, MonadIO m) ⇒ Yao → IPrecision → ℕ → m YaoNat
yaoNatNew yao pr share = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ YaoNat ^$ yaoReflect yao_nat32_new yao_nat_drop yao $ HS.fromIntegral share
  _                                → undefined

foreign import ccall unsafe "yao_nat32_constant" yao_nat32_constant ∷ Ptr CYao → CUInt → IO (Ptr CYaoNat)

yaoNatConstant ∷ (Monad m, MonadIO m) ⇒ Yao → IPrecision → ℕ → m YaoNat
yaoNatConstant yao pr value = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ YaoNat ^$ yaoReflect yao_nat32_constant yao_nat_drop yao $ HS.fromIntegral value
  _                                → undefined

foreign import ccall unsafe "yao_nat_mux" yao_nat_mux ∷ Ptr CYao → Ptr CYaoBool → Ptr CYaoNat → Ptr CYaoNat → IO (Ptr CYaoNat)

yaoNatMux ∷ (STACK, Monad m, MonadIO m) ⇒ Yao → YaoBool → YaoNat → YaoNat → m YaoNat
yaoNatMux yao b n₁ n₂ = io $ YaoNat ^$
  withYao yao $ \ yao →
  withForeignPtr (unYaoBool b) $ \ b →
  withForeignPtr (unYaoNat n₁) $ \ n₁ →
  withForeignPtr (unYaoNat n₂) $ \ n₂ →
  newForeignPtr yao_nat_drop *$ yao_nat_mux yao b n₁ n₂

foreign import ccall unsafe "yao_nat_add" yao_nat_add ∷ Ptr CYao → Ptr CYaoNat → Ptr CYaoNat → IO (Ptr CYaoNat)

yaoNatAdd ∷ (STACK, Monad m, MonadIO m) ⇒ Yao → YaoNat → YaoNat → m YaoNat
yaoNatAdd yao n₁ n₂ = io $ YaoNat ^$ yaoBinary yao_nat_add yao_nat_drop yao (unYaoNat n₁) (unYaoNat n₂)

foreign import ccall unsafe "yao_nat_mul" yao_nat_mul ∷ Ptr CYao → Ptr CYaoNat → Ptr CYaoNat → IO (Ptr CYaoNat)

yaoNatMul ∷ (STACK, Monad m, MonadIO m) ⇒ Yao → YaoNat → YaoNat → m YaoNat
yaoNatMul yao n₁ n₂ = io $ YaoNat ^$ yaoBinary yao_nat_mul yao_nat_drop yao (unYaoNat n₁) (unYaoNat n₂)

foreign import ccall unsafe "yao_nat_eq" yao_nat_eq ∷ Ptr CYao → Ptr CYaoNat → Ptr CYaoNat → IO (Ptr CYaoBool)

yaoNatEq ∷ (STACK, Monad m, MonadIO m) ⇒ Yao → YaoNat → YaoNat → m YaoBool
yaoNatEq yao n₁ n₂ = io $ YaoBool ^$ yaoBinary yao_nat_eq yao_bool_drop yao (unYaoNat n₁) (unYaoNat n₂)

foreign import ccall unsafe "yao_nat_lte" yao_nat_lte ∷ Ptr CYao → Ptr CYaoNat → Ptr CYaoNat → IO (Ptr CYaoBool)

yaoNatLte ∷ (STACK, Monad m, MonadIO m) ⇒ Yao → YaoNat → YaoNat → m YaoBool
yaoNatLte yao n₁ n₂ = io $ YaoBool ^$ yaoBinary yao_nat_lte yao_bool_drop yao (unYaoNat n₁) (unYaoNat n₂)

foreign import ccall unsafe "yao_nat32_get" yao_nat32_get ∷ Ptr CYao → Ptr CYaoNat → IO CUInt

yaoNatGet ∷ (Monad m, MonadIO m) ⇒ Yao → IPrecision → YaoNat → m ℕ
yaoNatGet yao pr share = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ HS.fromIntegral ^$ yaoReify yao_nat32_get yao (unYaoNat share)
  _                                 → undefined

foreign import ccall unsafe "&yao_nat_drop" yao_nat_drop ∷ FinalizerPtr CYaoNat

-- Delegation --

foreign import ccall unsafe "yao_share_send_nat32" yao_share_send_nat32 ∷ Ptr CPrg → Ptr (Ptr CChannel) → CSize → CUInt → IO ()

yaoShareSendNat ∷ (Monad m, MonadIO m) ⇒ Prg → 𝐿 Channel → IPrecision → ℕ → m ()
yaoShareSendNat prg chans pr input = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ yaoShareSend yao_share_send_nat32 prg chans $ HS.fromIntegral input
  _                                → undefined

foreign import ccall unsafe "yao_share_recv_nat32" yao_share_recv_nat32 ∷ Ptr CChannel → IO CUInt

yaoShareRecvNat ∷ (Monad m, MonadIO m) ⇒ Channel → IPrecision → m ℕ
yaoShareRecvNat chan pr = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ HS.fromIntegral ^$ yaoShareRecv yao_share_recv_nat32 chan
  _                                → undefined

foreign import ccall unsafe "yao_reveal_send_nat32" yao_reveal_send_nat32 ∷ Ptr CChannel → CUInt → IO ()

yaoRevealSendNat ∷ (Monad m, MonadIO m) ⇒ Channel → IPrecision → ℕ → m ()
yaoRevealSendNat chan pr output = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ yaoRevealSend yao_reveal_send_nat32 chan $ HS.fromIntegral output
  _                                → undefined

foreign import ccall unsafe "yao_reveal_recv_nat32" yao_reveal_recv_nat32 ∷ Ptr (Ptr CChannel) → CSize → IO CUInt

yaoRevealRecvNat ∷ (Monad m, MonadIO m) ⇒ 𝐿 Channel → IPrecision → m ℕ
yaoRevealRecvNat chans pr = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ HS.fromIntegral ^$ yaoRevealRecv yao_reveal_recv_nat32 chans
  _                                → undefined

yaoShareRecvYaoNat ∷ (Monad m, MonadIO m) ⇒ Yao → Channel → IPrecision → m YaoNat
yaoShareRecvYaoNat yao chan pr = do
  z ← yaoShareRecvNat chan pr
  yaoNatNew yao pr z

yaoRevealSendYaoNat ∷ (Monad m, MonadIO m) ⇒ Yao → Channel → IPrecision → YaoNat → m ()
yaoRevealSendYaoNat yao chan pr share = do
  z ← yaoNatGet yao pr share
  yaoRevealSendNat chan pr z

yaoReshareSendNat ∷ (Monad m, MonadIO m) ⇒ Yao → Prg → 𝐿 Channel → IPrecision → YaoNat → m ()
yaoReshareSendNat yao prg channels pr share = do
  n ← yaoNatGet yao pr share
  yaoShareSendNat prg channels pr n

yaoReshareRecvYaoNat ∷ (Monad m, MonadIO m) ⇒ Yao → 𝐿 Channel → IPrecision → m YaoNat
yaoReshareRecvYaoNat yao chans pr = do
  shares ← mapMOn chans $ \ chan → yaoShareRecvNat chan pr
  yaoNatNew yao pr $ fold 0 (BITS.xor) shares

--------------------------------
--- YAO Integer (Signed Int) ---
--------------------------------

foreign import ccall unsafe "yao_int32_new" yao_int32_new ∷ Ptr CYao → CInt → IO (Ptr CYaoInt)

yaoIntNew ∷ (Monad m, MonadIO m) ⇒ Yao → IPrecision → ℤ → m YaoInt
yaoIntNew yao pr share = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ YaoInt ^$ yaoReflect yao_int32_new yao_int_drop yao $ HS.fromIntegral share
  _                                → undefined

foreign import ccall unsafe "yao_int32_constant" yao_int32_constant ∷ Ptr CYao → CInt → IO (Ptr CYaoInt)

yaoIntConstant ∷ (Monad m, MonadIO m) ⇒ Yao → IPrecision → ℤ → m YaoInt
yaoIntConstant yao pr value = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ YaoInt ^$ yaoReflect yao_int32_constant yao_int_drop yao $ HS.fromIntegral value
  _                                → undefined

foreign import ccall unsafe "yao_int_add" yao_int_add ∷ Ptr CYao → Ptr CYaoInt → Ptr CYaoInt → IO (Ptr CYaoInt)

yaoIntAdd ∷ (STACK, Monad m, MonadIO m) ⇒ Yao → YaoInt → YaoInt → m YaoInt
yaoIntAdd yao z₁ z₂ = io $ YaoInt ^$ yaoBinary yao_int_add yao_int_drop yao (unYaoInt z₁) (unYaoInt z₂)

foreign import ccall unsafe "yao_int_sub" yao_int_sub ∷ Ptr CYao → Ptr CYaoInt → Ptr CYaoInt → IO (Ptr CYaoInt)

yaoIntSub ∷ (STACK, Monad m, MonadIO m) ⇒ Yao → YaoInt → YaoInt → m YaoInt
yaoIntSub yao z₁ z₂ = io $ YaoInt ^$ yaoBinary yao_int_sub yao_int_drop yao (unYaoInt z₁) (unYaoInt z₂)

foreign import ccall unsafe "yao_int_mul" yao_int_mul ∷ Ptr CYao → Ptr CYaoInt → Ptr CYaoInt → IO (Ptr CYaoInt)

yaoIntMul ∷ (STACK, Monad m, MonadIO m) ⇒ Yao → YaoInt → YaoInt → m YaoInt
yaoIntMul yao z₁ z₂ = io $ YaoInt ^$ yaoBinary yao_int_mul yao_int_drop yao (unYaoInt z₁) (unYaoInt z₂)

foreign import ccall unsafe "yao_int_div" yao_int_div ∷ Ptr CYao → Ptr CYaoInt → Ptr CYaoInt → IO (Ptr CYaoInt)

yaoIntDiv ∷ (STACK, Monad m, MonadIO m) ⇒ Yao → YaoInt → YaoInt → m YaoInt
yaoIntDiv yao z₁ z₂ = io $ YaoInt ^$ yaoBinary yao_int_div yao_int_drop yao (unYaoInt z₁) (unYaoInt z₂)

foreign import ccall unsafe "yao_int_mod" yao_int_mod ∷ Ptr CYao → Ptr CYaoInt → Ptr CYaoInt → IO (Ptr CYaoInt)

yaoIntMod ∷ (STACK, Monad m, MonadIO m) ⇒ Yao → YaoInt → YaoInt → m YaoInt
yaoIntMod yao z₁ z₂ = io $ YaoInt ^$ yaoBinary yao_int_mod yao_int_drop yao (unYaoInt z₁) (unYaoInt z₂)

foreign import ccall unsafe "yao_int_mux" yao_int_mux ∷ Ptr CYao → Ptr CYaoBool → Ptr CYaoInt → Ptr CYaoInt → IO (Ptr CYaoInt)

yaoIntMux ∷ (STACK, Monad m, MonadIO m) ⇒ Yao → YaoBool → YaoInt → YaoInt → m YaoInt
yaoIntMux yao b z₁ z₂ = io $ YaoInt ^$
  withYao yao $ \ yao →
  withForeignPtr (unYaoBool b) $ \ b →
  withForeignPtr (unYaoInt z₁) $ \ z₁ →
  withForeignPtr (unYaoInt z₂) $ \ z₂ →
  newForeignPtr yao_int_drop *$ yao_int_mux yao b z₁ z₂

foreign import ccall unsafe "yao_int_eq" yao_int_eq ∷ Ptr CYao → Ptr CYaoInt → Ptr CYaoInt → IO (Ptr CYaoBool)

yaoIntEq ∷ (STACK, Monad m, MonadIO m) ⇒ Yao → YaoInt → YaoInt → m YaoBool
yaoIntEq yao z₁ z₂ = io $ YaoBool ^$ yaoBinary yao_int_eq yao_bool_drop yao (unYaoInt z₁) (unYaoInt z₂)

foreign import ccall unsafe "yao_int_lte" yao_int_lte ∷ Ptr CYao → Ptr CYaoInt → Ptr CYaoInt → IO (Ptr CYaoBool)

yaoIntLte ∷ (STACK, Monad m, MonadIO m) ⇒ Yao → YaoInt → YaoInt → m YaoBool
yaoIntLte yao z₁ z₂ = io $ YaoBool ^$ yaoBinary yao_int_lte yao_bool_drop yao (unYaoInt z₁) (unYaoInt z₂)

foreign import ccall unsafe "yao_int_lt" yao_int_lt ∷ Ptr CYao → Ptr CYaoInt → Ptr CYaoInt → IO (Ptr CYaoBool)

yaoIntLt ∷ (STACK, Monad m, MonadIO m) ⇒ Yao → YaoInt → YaoInt → m YaoBool
yaoIntLt yao z₁ z₂ = io $ YaoBool ^$ yaoBinary yao_int_lt yao_bool_drop yao (unYaoInt z₁) (unYaoInt z₂)

foreign import ccall unsafe "yao_int32_get" yao_int32_get ∷ Ptr CYao → Ptr CYaoInt → IO CInt

yaoIntGet ∷ (Monad m, MonadIO m) ⇒ Yao → IPrecision → YaoInt → m ℤ
yaoIntGet yao pr share = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ HS.fromIntegral ^$ yaoReify yao_int32_get yao (unYaoInt share)
  _                                → undefined

foreign import ccall unsafe "&yao_int_drop" yao_int_drop ∷ FinalizerPtr CYaoInt

-- Delegation --

foreign import ccall unsafe "yao_share_send_int32" yao_share_send_int32 ∷ Ptr CPrg → Ptr (Ptr CChannel) → CSize → CInt → IO ()

yaoShareSendInt ∷ (Monad m, MonadIO m) ⇒ Prg → 𝐿 Channel → IPrecision → ℤ → m ()
yaoShareSendInt prg chans pr input = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ yaoShareSend yao_share_send_int32 prg chans $ HS.fromIntegral input
  _                                → undefined

foreign import ccall unsafe "yao_share_recv_int32" yao_share_recv_int32 ∷ Ptr CChannel → IO CInt

yaoShareRecvInt ∷ (Monad m, MonadIO m) ⇒ Channel → IPrecision → m ℤ
yaoShareRecvInt chan pr = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ HS.fromIntegral ^$ yaoShareRecv yao_share_recv_int32 chan
  _                                → undefined

foreign import ccall unsafe "yao_reveal_send_int32" yao_reveal_send_int32 ∷ Ptr CChannel → CInt → IO ()

yaoRevealSendInt ∷ (Monad m, MonadIO m) ⇒ Channel → IPrecision → ℤ → m ()
yaoRevealSendInt chan pr output = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ yaoRevealSend yao_reveal_send_int32 chan $ HS.fromIntegral output
  _                                → undefined

foreign import ccall unsafe "yao_reveal_recv_int32" yao_reveal_recv_int32 ∷ Ptr (Ptr CChannel) → CSize → IO CInt

yaoRevealRecvInt ∷ (Monad m, MonadIO m) ⇒ 𝐿 Channel → IPrecision → m ℤ
yaoRevealRecvInt chans pr = case pr of
  FixedIPr wPr dPr | wPr + dPr ≡ 32 → io $ HS.fromIntegral ^$ yaoRevealRecv yao_reveal_recv_int32 chans
  _                                → undefined

yaoShareRecvYaoInt ∷ (Monad m, MonadIO m) ⇒ Yao → Channel → IPrecision → m YaoInt
yaoShareRecvYaoInt yao chan pr = do
  z ← yaoShareRecvInt chan pr
  yaoIntNew yao pr z

yaoRevealSendYaoInt ∷ (Monad m, MonadIO m) ⇒ Yao → Channel → IPrecision → YaoInt → m ()
yaoRevealSendYaoInt yao chan pr share = do
  z ← yaoIntGet yao pr share
  yaoRevealSendInt chan pr z

yaoReshareSendInt ∷ (Monad m, MonadIO m) ⇒ Yao → Prg → 𝐿 Channel → IPrecision → YaoInt → m ()
yaoReshareSendInt yao prg channels pr share = do
  n ← yaoIntGet yao pr share
  yaoShareSendInt prg channels pr n

yaoReshareRecvYaoInt ∷ (Monad m, MonadIO m) ⇒ Yao → 𝐿 Channel → IPrecision → m YaoInt
yaoReshareRecvYaoInt yao chans pr = do
  shares ← mapMOn chans $ \ chan → yaoShareRecvInt chan pr
  yaoIntNew yao pr $ fold (HS.fromIntegral 0) (BITS.xor) shares
module Symphony.Dynamic.Par.Yao where
{-
import Symphony.Prelude

import Symphony.Lang.Syntax

import Symphony.Dynamic.Par.Error
import Symphony.Dynamic.Par.Types
import Symphony.Dynamic.Par.Dist.Types
import Symphony.Dynamic.Par.Lens

import Symphony.Dynamic.Par.Send
import Symphony.Dynamic.Par.EMP

import qualified Prelude as HS

empPublic ∷ ℤ8
empPublic = HS.fromIntegral 0

whoAmI ∷ IM DistVal PrinVal
whoAmI = askL iCxtMeL

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
-}
