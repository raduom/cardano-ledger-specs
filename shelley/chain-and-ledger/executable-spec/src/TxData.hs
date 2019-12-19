{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module TxData
  where

import           Cardano.Binary (FromCBOR (fromCBOR), ToCBOR (toCBOR), decodeListLen, decodeWord,
                     encodeBreak, encodeListLen, encodeListLenIndef, encodeMapLen, encodeWord)
import           Cardano.Ledger.Shelley.Crypto
import           Cardano.Prelude (NoUnexpectedThunks (..), Word64)
import           Lens.Micro.TH (makeLenses)

import           Data.Foldable (foldMap)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Ord (comparing)
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Set (Set)
import           Data.Typeable (Typeable)
import           Data.Word (Word8)
import           GHC.Generics (Generic)
import           Numeric.Natural (Natural)

import           BaseTypes (UnitInterval)
import           Coin (Coin)
import           Keys (AnyKeyHash, pattern AnyKeyHash, GenKeyHash, Hash, KeyHash, Sig, VKey,
                     VKeyGenesis, VerKeyVRF, hashAnyKey)
import           Ledger.Core (Relation (..))
import           Slot (Epoch, Slot)
import           Updates (Update, updateNull)
import           Scripts
import           Value
import           CostModel
import           PParams (PlutusPP)
import           Serialization (CBORGroup (..), ToCBORGroup (..))
>>>>>>> 6791a673... CBOR serialization adjustments of Shelley txns

-- |The delegation of one stake key to another.
data Delegation crypto = Delegation
  { _delegator :: Credential crypto
  , _delegatee :: KeyHash crypto
  } deriving (Eq, Generic, Show)

instance NoUnexpectedThunks (Delegation crypto)

-- |A stake pool.
data PoolParams crypto =
  PoolParams
    { _poolPubKey  :: KeyHash crypto
    , _poolVrf     :: Hash (HASH crypto) (VerKeyVRF (VRF crypto))
    , _poolPledge  :: Coin
    , _poolCost    :: Coin
    , _poolMargin  :: UnitInterval
    , _poolRAcnt   :: RewardAcnt crypto
    , _poolOwners  :: Set (KeyHash crypto)
    } deriving (Show, Generic, Eq)
      deriving ToCBOR via CBORGroup (PoolParams crypto)

instance NoUnexpectedThunks (PoolParams crypto)

-- |An account based address for rewards
newtype RewardAcnt crypto = RewardAcnt
  { getRwdCred :: StakeCredential crypto
  } deriving (Show, Eq, NoUnexpectedThunks, Ord)

-- | Script hash or key hash for a payment or a staking object.
data Credential crypto =
    ScriptHashObj (ScriptHash crypto)
  | KeyHashObj    (KeyHash crypto)
  | GenesisHashObj (GenKeyHash crypto)
    deriving (Show, Eq, Generic, Ord)
    deriving ToCBOR via (CBORGroup (Credential crypto))

instance NoUnexpectedThunks (Credential crypto)


-- |An address for UTxO.
data Addr crypto
  = AddrBase (Credential crypto) (Credential crypto)
  | AddrEnterprise (Credential crypto)
  | AddrPtr (Credential crypto) Ptr
  | AddrBootstrap (KeyHash crypto)
  deriving (Show, Eq, Ord, Generic)

instance NoUnexpectedThunks (Addr crypto)

type Ix  = Natural

-- | Pointer to a slot, transaction index and index in certificate list.
data Ptr
  = Ptr Slot Ix Ix
  deriving (Show, Eq, Ord, Generic)

instance NoUnexpectedThunks Ptr

-- | A simple language for expressing conditions under which it is valid to
-- withdraw from a normal UTxO payment address or to use a stake address.
--
-- The use case is for expressing multi-signature payment addresses and
-- multi-signature stake addresses. These can be combined arbitrarily using
-- logical operations:
--
-- * multi-way \"and\";
-- * multi-way \"or\";
-- * multi-way \"N of M\".
--
-- This makes it easy to express multi-signature addresses, and provides an
-- extension point to express other validity conditions, e.g., as needed for
-- locking funds used with lightning.
--
data MultiSig crypto =
       -- | Require the redeeming transaction be witnessed by the spending key
       --   corresponding to the given verification key hash.
       RequireSignature   (AnyKeyHash crypto)

       -- | Require all the sub-terms to be satisfied.
     | RequireAllOf      [MultiSig crypto]

       -- | Require any one of the sub-terms to be satisfied.
     | RequireAnyOf      [MultiSig crypto]

       -- | Require M of the given sub-terms to be satisfied.
     | RequireMOf    Int [MultiSig crypto]
  deriving (Show, Eq, Ord, Generic)

instance NoUnexpectedThunks (MultiSig crypto)

newtype ScriptHash crypto =
  ScriptHash (Hash (HASH crypto) (MultiSig crypto))
  deriving (Show, Eq, Ord, NoUnexpectedThunks)

deriving instance Crypto crypto => ToCBOR (ScriptHash crypto)

type Wdrl crypto = Map (RewardAcnt crypto) Coin

-- |A unique ID of a transaction, which is computable from the transaction.
newtype TxId crypto
  = TxId { _TxId :: Hash (HASH crypto) (TxBody crypto) }
  deriving (Show, Eq, Ord, NoUnexpectedThunks)

deriving instance Crypto crypto => ToCBOR (TxId crypto)

-- |The input of a UTxO.
data TxIn crypto
  = TxIn (TxId crypto) Natural
  deriving (Show, Eq, Generic, Ord)

instance NoUnexpectedThunks (TxIn crypto)

-- |The output of a UTxO.
data TxOut crypto
  = TxOut (Addr crypto) Coin
  deriving (Show, Eq, Generic, Ord)

instance NoUnexpectedThunks (TxOut crypto)

type StakeCredential crypto = Credential crypto

-- | A heavyweight certificate.
data DCert crypto
    -- | A stake key registration certificate.
  = RegKey (StakeCredential crypto)
    -- | A stake key deregistration certificate.
  | DeRegKey (StakeCredential crypto)
    -- | A stake pool registration certificate.
  | RegPool (PoolParams crypto)
    -- | A stake pool retirement certificate.
  | RetirePool (KeyHash crypto) Epoch
    -- | A stake delegation certificate.
  | Delegate (Delegation crypto)
    -- | Genesis key delegation certificate
  | GenesisDelegate (GenKeyHash crypto, KeyHash crypto)
    -- | Move instantaneous rewards certificate
  | InstantaneousRewards (Map (Credential crypto) Coin)
  deriving (Show, Generic, Eq)

instance NoUnexpectedThunks (DCert crypto)

-- |A raw transaction
data TxBody crypto
  = TxBody
      { _inputs   :: !(Set (TxIn crypto))
      , _outputs  :: [TxOut crypto]
      , _certs    :: Seq (DCert crypto)
      , _wdrls    :: Wdrl crypto
      , _txfee    :: Coin
      , _ttl      :: Slot
      , _txUpdate :: Update crypto
      } deriving (Show, Eq, Generic)

instance NoUnexpectedThunks (TxBody crypto)

-- |Proof/Witness that a transaction is authorized by the given key holder.
data WitVKey crypto
  = WitVKey (VKey crypto) !(Sig crypto (TxBody crypto))
  | WitGVKey (VKeyGenesis crypto) !(Sig crypto (TxBody crypto))
  deriving (Show, Eq, Generic)

instance Crypto crypto => NoUnexpectedThunks (WitVKey crypto)

witKeyHash
  :: forall crypto. ( Crypto crypto)
  => WitVKey crypto
  -> AnyKeyHash crypto
witKeyHash (WitVKey key _) = hashAnyKey key
witKeyHash (WitGVKey key _) = hashAnyKey key

instance forall crypto
  . ( Crypto crypto)
  => Ord (WitVKey crypto) where
    compare = comparing witKeyHash

-- |A fully formed transaction.
data Tx crypto
  = Tx
      { _body           :: !(TxBody crypto)
      , _witnessVKeySet :: !(Set (WitVKey crypto))
      , _witnessMSigMap ::
          Map (ScriptHash crypto) (MultiSig crypto)
      } deriving (Show, Eq, Generic)

instance Crypto crypto => NoUnexpectedThunks (Tx crypto)

newtype StakeCreds crypto =
  StakeCreds (Map (StakeCredential crypto) Slot)
  deriving (Show, Eq, NoUnexpectedThunks)

addStakeCreds :: (StakeCredential crypto) -> Slot -> (StakeCreds crypto) -> StakeCreds crypto
addStakeCreds newCred s (StakeCreds creds) = StakeCreds $ Map.insert newCred s creds

newtype StakePools crypto =
  StakePools (Map (KeyHash crypto) Slot)
  deriving (Show, Eq, NoUnexpectedThunks)


-- CBOR

instance
  (Crypto crypto)
  => ToCBOR (DCert crypto)
 where
  toCBOR = \case
    RegKey (KeyHashObj h) ->
      encodeListLen 2
        <> toCBOR (0 :: Word8)
        <> toCBOR h
    RegKey (ScriptHashObj h) ->
      encodeListLen 2
        <> toCBOR (1 :: Word8)
        <> toCBOR h
    RegKey (GenesisHashObj _) -> error "We need to fix credential type"

    DeRegKey (KeyHashObj h) ->
      encodeListLen 2
        <> toCBOR (2 :: Word8)
        <> toCBOR h
    DeRegKey (ScriptHashObj h) ->
      encodeListLen 2
        <> toCBOR (3 :: Word8)
        <> toCBOR h
    DeRegKey (GenesisHashObj _) -> error "We need to fix credential type"

    Delegate (Delegation (KeyHashObj h) poolkh) ->
      encodeListLen 3
        <> toCBOR (4 :: Word8)
        <> toCBOR h
        <> toCBOR poolkh
    Delegate (Delegation (ScriptHashObj h) poolkh) ->
      encodeListLen 3
        <> toCBOR (5 :: Word8)
        <> toCBOR h
        <> toCBOR poolkh
    Delegate (Delegation (GenesisHashObj _) _) -> error "We need to fix credential type"

    RegPool poolParams ->
      encodeListLen (1 + listLen poolParams)
        <> toCBOR (6 :: Word8)
        <> toCBORGroup poolParams

    RetirePool vk epoch ->
      encodeListLen 3
        <> toCBOR (7 :: Word8)
        <> toCBOR vk
        <> toCBOR epoch

    GenesisDelegate (gk, dk) ->
      encodeListLen 3
        <> toCBOR (8 :: Word8)
        <> toCBOR gk
        <> toCBOR dk

    InstantaneousRewards credCoinMap ->
      encodeListLen 2
        <> toCBOR (9 :: Word8)
        <> toCBOR credCoinMap

instance
  (Typeable crypto, Crypto crypto)
  => ToCBOR (TxIn crypto)
 where
  toCBOR (TxIn txId index) =
    encodeListLen 2
      <> toCBOR txId
      <> toCBOR (fromIntegral index :: Word64)

instance
  (Typeable crypto, Crypto crypto)
  => ToCBOR (TxOut crypto)
 where
  toCBOR (TxOut addr coin) =
    encodeListLen 2
      <> toCBOR addr
      <> toCBOR coin

instance
  Crypto crypto
  => ToCBOR (WitVKey crypto)
 where
  toCBOR (WitVKey vk sig) =
    encodeListLen 2
      <> toCBOR vk
      <> toCBOR sig
  toCBOR (WitGVKey vk sig) =
    encodeListLen 2
      <> toCBOR vk
      <> toCBOR sig


instance
  (Crypto crypto)
  => ToCBOR (Tx crypto)
 where
  toCBOR tx =
    encodeListLen 3
      <> toCBOR (_body tx)
      <> toCBOR (_witnessVKeySet tx)
      <> toCBOR (_witnessMSigMap tx)

newtype CborSeq a = CborSeq (Seq a)

instance ToCBOR a => ToCBOR (CborSeq a) where
  toCBOR (CborSeq xs) =
    let l = fromIntegral $ Seq.length xs
        contents = foldMap toCBOR xs
    in
    if l <= 23
    then encodeListLen l <> contents
    else encodeListLenIndef <> contents <> encodeBreak

instance
  (Crypto crypto)
  => ToCBOR (TxBody crypto)
 where
  toCBOR txbody =
    let l = toList $
              single (encodeWord 0 <> toCBOR (_inputs txbody))
            . single (encodeWord 1 <> toCBOR (_outputs txbody))
            . single (encodeWord 2 <> toCBOR (_txfee txbody))
            . single (encodeWord 3 <> toCBOR (_ttl txbody))
            . if null cs then none else single (encodeWord 4 <> toCBOR (CborSeq cs))
            . if null ws then none else single (encodeWord 5 <> toCBOR ws)
            . if updateNull us then none else single (encodeWord 6 <> toCBOR us)
        toList xs = xs []
        single x = (x:)
        none = id
        n = fromIntegral $ length l
    in encodeMapLen n <> foldr (<>) mempty l
    where
      cs = _certs txbody
      ws = _wdrls txbody
      us = _txUpdate txbody

instance ( Crypto crypto) =>
  ToCBOR (MultiSig crypto) where
  toCBOR (RequireSignature hk) =
    encodeListLen 2 <> encodeWord 0 <> toCBOR hk
  toCBOR (RequireAllOf msigs) =
    encodeListLen 2 <> encodeWord 1 <> toCBOR msigs
  toCBOR (RequireAnyOf msigs) =
    encodeListLen 2 <> encodeWord 2 <> toCBOR msigs
  toCBOR (RequireMOf m msigs) =
    encodeListLen 3 <> encodeWord 3 <> toCBOR m <> toCBOR msigs

instance ( Crypto crypto) =>
  FromCBOR (MultiSig crypto) where
  fromCBOR = do
    _ <- decodeListLen
    ctor <- decodeWord
    case ctor of
      0 -> do
       hk <- AnyKeyHash <$> fromCBOR
       pure $ RequireSignature hk
      1 -> do
        msigs <- fromCBOR
        pure $ RequireAllOf msigs
      2 -> do
        msigs <- fromCBOR
        pure $ RequireAnyOf msigs
      3 -> do
        m     <- fromCBOR
        msigs <- fromCBOR
        pure $ RequireMOf m msigs
      _ -> error "pattern no supported"


instance (Typeable crypto, Crypto crypto)
  => ToCBORGroup (Credential crypto) where
  listLen _ = 2
  toCBORGroup = \case
    KeyHashObj     kh -> toCBOR (0 :: Word8) <> toCBOR kh
    ScriptHashObj  hs -> toCBOR (1 :: Word8) <> toCBOR hs
    GenesisHashObj kh -> toCBOR (2 :: Word8) <> toCBOR kh

instance
  (Typeable crypto, Crypto crypto)
  => ToCBOR (Addr crypto)
 where
  toCBOR (AddrBase       (KeyHashObj a)    (KeyHashObj b))      =
    encodeListLen 3 <> toCBOR (0 :: Word8)  <> toCBOR a       <> toCBOR b
  toCBOR (AddrBase       (KeyHashObj a)     (ScriptHashObj b))  =
    encodeListLen 3 <> toCBOR (1 :: Word8)  <> toCBOR a       <> toCBOR b
  toCBOR (AddrBase       (ScriptHashObj a)  (KeyHashObj b))     =
    encodeListLen 3 <> toCBOR (2 :: Word8)  <> toCBOR a       <> toCBOR b
  toCBOR (AddrBase       (ScriptHashObj a) (ScriptHashObj b))   =
    encodeListLen 3 <> toCBOR (3 :: Word8)  <> toCBOR a       <> toCBOR b
  toCBOR (AddrPtr        (KeyHashObj a)    pointer)             =
    encodeListLen (2 + listLen pointer)
    <> toCBOR (4 :: Word8)
    <> toCBOR a
    <> toCBORGroup pointer
  toCBOR (AddrPtr        (ScriptHashObj a)  pointer)            =
    encodeListLen (2 + listLen pointer)
    <> toCBOR (5 :: Word8)
    <> toCBOR a
    <> toCBORGroup pointer
  toCBOR (AddrEnterprise (KeyHashObj a))                        =
    encodeListLen 2 <> toCBOR (6 :: Word8)  <> toCBOR a
  toCBOR (AddrEnterprise (ScriptHashObj a))                     =
    encodeListLen 2 <> toCBOR (7 :: Word8)  <> toCBOR a
  toCBOR (AddrBootstrap  a)                                     =
    encodeListLen 2 <> toCBOR (8 :: Word8)  <> toCBOR a
  toCBOR _ = error "this should be unreachable" -- TODO fix me


instance ToCBORGroup Ptr where
  toCBORGroup (Ptr sl txIx certIx) =
         toCBOR sl
      <> toCBOR (fromInteger (toInteger txIx) :: Word)
      <> toCBOR (fromInteger (toInteger certIx) :: Word)
  listLen _ = 3


instance
  (Crypto crypto)
  => ToCBORGroup (PoolParams crypto)
 where
  toCBORGroup poolParams =
         toCBOR (_poolOwners poolParams)
      <> toCBOR (_poolCost poolParams)
      <> toCBOR (_poolMargin poolParams)
      <> toCBOR (_poolPledge poolParams)
      <> toCBOR (_poolPubKey poolParams)
      <> toCBOR (_poolVrf poolParams)
      <> toCBOR (_poolRAcnt poolParams)
  listLen _ = 7

instance Crypto crypto
  => ToCBOR (RewardAcnt crypto) where
  toCBOR (RewardAcnt ra) = toCBOR ra

instance Relation (StakeCreds crypto) where
  type Domain (StakeCreds crypto) = StakeCredential crypto
  type Range (StakeCreds crypto)  = Slot

  singleton k v = StakeCreds $ Map.singleton k v

  dom (StakeCreds stkCreds) = dom stkCreds

  range (StakeCreds stkCreds) = range stkCreds

  s ◁ (StakeCreds stkCreds) = StakeCreds $ s ◁ stkCreds

  s ⋪ (StakeCreds stkCreds) = StakeCreds $ s ⋪ stkCreds

  (StakeCreds stkCreds) ▷ s = StakeCreds $ stkCreds ▷ s

  (StakeCreds stkCreds) ⋫ s = StakeCreds $ stkCreds ⋫ s

  (StakeCreds a) ∪ (StakeCreds b) = StakeCreds $ a ∪ b

  (StakeCreds a) ⨃ b = StakeCreds $ a ⨃ b

  vmax <=◁ (StakeCreds stkCreds) = StakeCreds $ vmax <=◁ stkCreds

  (StakeCreds stkCreds) ▷<= vmax = StakeCreds $ stkCreds ▷<= vmax

  (StakeCreds stkCreds) ▷>= vmin = StakeCreds $ stkCreds ▷>= vmin

  size (StakeCreds stkCreds) = size stkCreds

-- Lenses

makeLenses ''TxBody

makeLenses ''Tx

makeLenses ''Delegation

makeLenses ''PoolParams
