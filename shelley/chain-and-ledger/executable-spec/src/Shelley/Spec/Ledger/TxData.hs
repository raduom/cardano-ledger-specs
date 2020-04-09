{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Shelley.Spec.Ledger.TxData
  where

import           Cardano.Binary (FromCBOR (fromCBOR), ToCBOR (toCBOR), decodeListLen, decodeWord,
                     encodeListLen, encodeMapLen, encodeWord, enforceSize, matchSize)
import           Cardano.Prelude (NoUnexpectedThunks (..), Word64, catMaybes)
import           Control.Monad (unless)
import           Shelley.Spec.Ledger.Crypto

import           Data.ByteString (ByteString)
import           Data.Foldable (fold)
import           Data.Map.Strict (Map, filterWithKey)
import qualified Data.Map.Strict as Map
import           Data.Ord (comparing)
import           Data.Sequence.Strict (StrictSeq)
import qualified Data.Sequence.Strict as StrictSeq
import           Data.Set (Set, filter)
import qualified Data.Set as Set
import           Data.Typeable (Typeable)
import           Data.Word (Word8)
import           GHC.Generics (Generic)
import           Numeric.Natural (Natural)

import           Byron.Spec.Ledger.Core (Relation (..))
import           Shelley.Spec.Ledger.BaseTypes (StrictMaybe (..), Text64, UnitInterval, invalidKey,
                     strictMaybeToMaybe)
import           Shelley.Spec.Ledger.Coin (Coin (..))
import           Shelley.Spec.Ledger.Keys (AnyKeyHash, GenKeyHash, Hash, KeyHash, pattern KeyHash,
                     Sig, VKey, VerKeyVRF, hashAnyKey)
import           Shelley.Spec.Ledger.MetaData (MetaDataHash)
import           Shelley.Spec.Ledger.PParams (Update, PPHash(..))
import           Shelley.Spec.Ledger.Slot (EpochNo (..), SlotNo (..))

import           Shelley.Spec.Ledger.Serialization (CBORGroup (..), CborSeq (..),
                     FromCBORGroup (..), ToCBORGroup (..), decodeMapContents, mapFromCBOR,
                     mapToCBOR, unwrapCborStrictSeq)

import           Shelley.Spec.Ledger.Scripts
import           Shelley.Spec.Ledger.Value
import           Shelley.Spec.Ledger.CostModel

-- |The delegation of one stake key to another.
data Delegation crypto = Delegation
  { _delegator :: !(Credential crypto)
  , _delegatee :: !(KeyHash crypto)
  } deriving (Eq, Generic, Show)

instance NoUnexpectedThunks (Delegation crypto)

newtype Url = Url { unUrl :: Text64 }
  deriving (Eq, Generic, Show, ToCBOR, FromCBOR, NoUnexpectedThunks)

data PoolMetaData = PoolMetaData
  { _poolMDUrl  :: !Url
  , _poolMDHash :: !ByteString
  } deriving (Eq, Generic, Show)

instance NoUnexpectedThunks PoolMetaData

-- |A stake pool.
data PoolParams crypto =
  PoolParams
    { _poolPubKey  :: !(KeyHash crypto)
    , _poolVrf     :: !(Hash (HASH crypto) (VerKeyVRF (VRF crypto)))
    , _poolPledge  :: !Coin
    , _poolCost    :: !Coin
    , _poolMargin  :: !UnitInterval
    , _poolRAcnt   :: !(RewardAcnt crypto)
    , _poolOwners  :: !(Set (KeyHash crypto))
    , _poolRelays  :: !(StrictSeq Url)
    , _poolMD      :: !(StrictMaybe PoolMetaData)
    } deriving (Show, Generic, Eq)
      deriving ToCBOR via CBORGroup (PoolParams crypto)
      deriving FromCBOR via CBORGroup (PoolParams crypto)

instance NoUnexpectedThunks (PoolParams crypto)

-- |An account based address for rewards
newtype RewardAcnt crypto = RewardAcnt
  { getRwdCred :: Credential crypto
  } deriving (Show, Eq, NoUnexpectedThunks, Ord, FromCBOR, ToCBOR)

-- | Script hash or key hash for a payment or a staking object.
data Credential crypto =
    ScriptHashObj !(ScriptHash crypto)
  | KeyHashObj    !(KeyHash crypto)
    deriving (Show, Eq, Generic, Ord)
    deriving ToCBOR via (CBORGroup (Credential crypto))

newtype GenesisCredential crypto = GenesisCredential (GenKeyHash crypto)
  deriving (Show, Generic)

instance Ord (GenesisCredential crypto)
  where compare (GenesisCredential gh) (GenesisCredential gh')  = compare gh gh'

instance Eq (GenesisCredential crypto)
  where (==) (GenesisCredential gh) (GenesisCredential gh') = gh == gh'

instance NoUnexpectedThunks (Credential crypto)

type PaymentCredential crypto = Credential crypto
type StakeCredential crypto = Credential crypto

data StakeReference crypto
  = StakeRefBase !(StakeCredential crypto)
  | StakeRefPtr !Ptr
  | StakeRefNull
  deriving (Show, Eq, Ord, Generic)

instance NoUnexpectedThunks (StakeReference crypto)

-- |An address for UTxO.
data Addr crypto
  = Addr !(PaymentCredential crypto) !(StakeReference crypto)
  | AddrBootstrap !(KeyHash crypto)
  deriving (Show, Eq, Ord, Generic)
  deriving (ToCBOR, FromCBOR) via (CBORGroup (Addr crypto))

instance NoUnexpectedThunks (Addr crypto)

type Ix  =  Natural

-- | Pointer to a slot, transaction index and index in certificate list.
data Ptr
  = Ptr !SlotNo !Ix !Ix
  deriving (Show, Eq, Ord, Generic)
  deriving (ToCBOR, FromCBOR) via CBORGroup Ptr

instance NoUnexpectedThunks Ptr


newtype Wdrl crypto = Wdrl { unWdrl :: Map (RewardAcnt crypto) Coin }
  deriving (Show, Eq, Generic, NoUnexpectedThunks)

instance Crypto crypto => ToCBOR (Wdrl crypto) where
  toCBOR = mapToCBOR . unWdrl

instance Crypto crypto => FromCBOR (Wdrl crypto) where
  fromCBOR = Wdrl <$> mapFromCBOR

-- | types of things scripts can be used to validate
data ScrTypes = InputTag | ForgeTag | CertTag | WdrlTag
  deriving (Show, Eq, Ord, Generic)

instance NoUnexpectedThunks ScrTypes

-- | pointer to the thing the redeemer is for
data RdmrPtr = RdmrPtr
  {   scrType :: ScrTypes
    , rix      :: Ix }
  deriving (Show, Eq, Ord, Generic)

instance NoUnexpectedThunks RdmrPtr

-- | data structure of indexed redeemers
data Rdmrs = Rdmrs (Map RdmrPtr Data)
  deriving (Show, Eq, Ord, Generic)

instance NoUnexpectedThunks Rdmrs

-- | hash of the indexed redeemer structure in the Tx
newtype RdmrsHash crypto
  = RdmrsHash { _rh :: Hash (HASH crypto) Rdmrs }
  deriving (Show, Eq, Ord, NoUnexpectedThunks)

deriving instance Crypto crypto => ToCBOR (RdmrsHash crypto)
deriving instance Crypto crypto => FromCBOR (RdmrsHash crypto)

-- -- | get value from Tx output
-- getValueTx :: TxOut crypto -> Value crypto
-- getValueTx (TxOut _ v) = v
--
-- -- | get address from Tx output
-- getAddressTx :: TxOut crypto -> Addr crypto
-- getAddressTx (TxOut a _) = a

-- |A unique ID of a transaction, which is computable from the transaction.
newtype TxId crypto
  = TxId { _TxId :: Hash (HASH crypto) (TxBody crypto) }
  deriving (Show, Eq, Ord, NoUnexpectedThunks)

deriving instance Crypto crypto => ToCBOR (TxId crypto)
deriving instance Crypto crypto => FromCBOR (TxId crypto)

-- |The input of a UTxO.
data UTxOIn crypto
  = UTxOIn (TxId crypto) Natural -- TODO use our own Natural type
  deriving (Show, Eq, Generic, Ord)

instance NoUnexpectedThunks (UTxOIn crypto)

-- | get Tx inputs marked as for-fees
txinputsvf :: Set (TxIn crypto) -> Set (TxIn crypto)
txinputsvf ins = Set.filter (\(TxIn _ _ isf) -> isf == IsFee Yes) ins

-- | get UTxOIn reference from Tx input
utxoref :: TxIn crypto -> UTxOIn crypto
utxoref (TxIn txid ix _) = UTxOIn txid ix

-- | get value from UTxO output
getValue :: Crypto crypto => UTxOOut crypto -> Value crypto
getValue (UTxOOutND (XOutND   _ v)   _) = compactValueToValue v
getValue (UTxOOutPT (UTxOOutP _ v _) _) = compactValueToValue v

-- | get address from UTxO output
getAddress :: UTxOOut crypto -> Addr crypto
getAddress (UTxOOutND (XOutND   a _)   _) = a
getAddress (UTxOOutPT (UTxOOutP a _ _) _) = a

-- | get address from UTxO output
getCoin :: Crypto crypto => UTxOOut crypto -> Coin
getCoin (UTxOOutND (XOutND   _ v)   _) =
  getAdaAmount $ Value $ filterWithKey (\k _ -> k==adaID) v'
  where
    Value v' = compactValueToValue v
getCoin (UTxOOutPT (UTxOOutP _ v _) _) =
  getAdaAmount $ Value $ filterWithKey (\k _ -> k==adaID) v'
  where
    Value v' = compactValueToValue v

-- |The input of a Tx.
data TxIn crypto
  = TxIn !(TxId crypto) !Natural IsFee -- TODO use our own Natural type
  deriving (Show, Eq, Generic, Ord)

instance NoUnexpectedThunks (TxIn crypto)

-- |The output of a Tx.
data TxOutP crypto = TxOutP (Addr crypto) (Value crypto) (DataHash crypto)
  deriving (Show, Eq, Generic, Ord)

-- |A plutus output of a UTxO.
data UTxOOutP crypto = UTxOOutP (Addr crypto) (CompactValue crypto) (DataHash crypto)
  deriving (Show, Eq, Generic, Ord)

instance NoUnexpectedThunks (TxOutP crypto)
instance NoUnexpectedThunks (UTxOOutP crypto)

-- | current item - things that might need validation
data CurItem crypto
  = SH (ScriptHash crypto) | TI (TxIn crypto) | WD (RewardAcnt crypto) | DC (DCert crypto)
  deriving (Show, Eq, Generic)

instance NoUnexpectedThunks (CurItem crypto)

-- |The output of a UTxO.
data UTxOOut crypto
  = UTxOOutND (XOutND crypto) SlotNo | UTxOOutPT (UTxOOutP crypto) SlotNo
  deriving (Show, Eq, Generic, Ord)


-- |The output of a Tx  without data value.
data OutND crypto
  = OutND (Addr crypto) (Value crypto)
  deriving (Show, Eq, Generic, Ord)

-- |The output of a UTxO without data value.
data XOutND crypto
  = XOutND (Addr crypto) (CompactValue crypto)
  deriving (Show, Eq, Generic, Ord)

instance NoUnexpectedThunks (OutND crypto)
instance NoUnexpectedThunks (XOutND crypto)

-- |The output of a Tx.
data TxOut crypto
  = TxOutND !(OutND crypto) | TxOutPT !(TxOutP crypto) HasDV
  deriving (Show, Eq, Generic, Ord)

instance NoUnexpectedThunks (TxOut crypto)

instance NoUnexpectedThunks (UTxOOut crypto)

data DelegCert crypto =
    -- | A stake key registration certificate.
    RegKey !(Credential crypto)
    -- | A stake key deregistration certificate.
  | DeRegKey !(Credential crypto)
    -- | A stake delegation certificate.
  | Delegate !(Delegation crypto)
  deriving (Show, Generic, Eq)

data PoolCert crypto =
    -- | A stake pool registration certificate.
    RegPool !(PoolParams crypto)
    -- | A stake pool retirement certificate.
  | RetirePool !(KeyHash crypto) !EpochNo
  deriving (Show, Generic, Eq)

-- | Genesis key delegation certificate
data GenesisDelegate crypto =
    GenesisDelegate !(GenKeyHash crypto) !(KeyHash crypto)
  deriving (Show, Generic, Eq)

-- | Move instantaneous rewards certificate
newtype MIRCert crypto = MIRCert (Map (Credential crypto) Coin)
  deriving (Show, Generic, Eq)

instance Crypto crypto => FromCBOR (MIRCert crypto) where
  fromCBOR = MIRCert <$> mapFromCBOR

instance Crypto crypto => ToCBOR (MIRCert crypto) where
  toCBOR (MIRCert c) = mapToCBOR c

-- | A heavyweight certificate.
data DCert crypto =
    DCertDeleg !(DelegCert crypto)
  | DCertPool !(PoolCert crypto)
  | DCertGenesis !(GenesisDelegate crypto)
  | DCertMir !(MIRCert crypto)
  deriving (Show, Generic, Eq)

instance NoUnexpectedThunks (DelegCert crypto)
instance NoUnexpectedThunks (PoolCert crypto)
instance NoUnexpectedThunks (GenesisDelegate crypto)
instance NoUnexpectedThunks (MIRCert crypto)
instance NoUnexpectedThunks (DCert crypto)

-- |A raw transaction
data TxBody crypto
  = TxBody
      { _inputs   :: !(Set (TxIn crypto))
      , _outputs  :: !(StrictSeq (TxOut crypto))
      , _certs    :: !(StrictSeq (DCert crypto))
      , _forge    :: !Value crypto
      , _exunits  :: !ExUnits --TODO Maybe type
      , _wdrls    :: !Wdrl crypto
      , _txfee    :: !Coin
      , _fst      :: !SlotNo
      , _ttl      :: !SlotNo
      , _txUpdate :: !(StrictMaybe (Update crypto))
      , _ppHash   :: !(StrictMaybe (PPHash crypto))
      , _rdmrsHash:: !(StrictMaybe (RdmrsHash crypto))
      , _mdHash   :: !(StrictMaybe (MetaDataHash crypto))
      } deriving (Show, Eq, Generic)

instance NoUnexpectedThunks (TxBody crypto)

-- |transaction witness data
data TxWitness crypto
  = TxWitness
      { _witnessVKeySet :: !(Set (WitVKey crypto))
      , _scripts        :: !(Set (Script crypto))
      , _dats           :: !(Set Data)
      , _rdmrs          :: Rdmrs
      } deriving (Show, Eq, Generic)

instance Crypto crypto => NoUnexpectedThunks (TxWitness crypto)


-- |Proof/Witness that a transaction is authorized by the given key holder.
data WitVKey crypto
  = WitVKey !(VKey crypto) !(Sig crypto (TxBody crypto))
  deriving (Show, Eq, Generic)

instance Crypto crypto => NoUnexpectedThunks (WitVKey crypto)

witKeyHash
  :: forall crypto. ( Crypto crypto)
  => WitVKey crypto
  -> AnyKeyHash crypto
witKeyHash (WitVKey key _) = hashAnyKey key

instance forall crypto
  . ( Crypto crypto)
  => Ord (WitVKey crypto) where
    compare = comparing witKeyHash

newtype StakeCreds crypto =
  StakeCreds (Map (Credential crypto) SlotNo)
  deriving (Show, Eq, ToCBOR, FromCBOR, NoUnexpectedThunks)

addStakeCreds :: (Credential crypto) -> SlotNo -> (StakeCreds crypto) -> StakeCreds crypto
addStakeCreds newCred s (StakeCreds creds) = StakeCreds $ Map.insert newCred s creds

newtype StakePools crypto =
  StakePools { unStakePools :: (Map (KeyHash crypto) SlotNo) }
  deriving (Show, Eq, ToCBOR, FromCBOR, NoUnexpectedThunks)


-- CBOR

instance FromCBOR RdmrPtr
 where
   fromCBOR = do
     enforceSize "RdmrPtr" 2
     a <- fromCBOR
     b <- fromCBOR
     pure $ RdmrPtr a b


instance ToCBOR RdmrPtr
 where
   toCBOR rp =
     encodeListLen 2
       <> toCBOR (scrType rp)
       <> toCBOR (rix rp)


instance
  (Crypto crypto)
  => ToCBOR (CurItem crypto)
 where
   toCBOR = \case
     SH a ->
       encodeListLen 2
         <> toCBOR (0 :: Word8)
         <> toCBOR a
     TI a ->
       encodeListLen 2
         <> toCBOR (1 :: Word8)
         <> toCBOR a
     WD a ->
       encodeListLen 2
         <> toCBOR (2 :: Word8)
         <> toCBOR a
     DC a ->
       encodeListLen 2
         <> toCBOR (3 :: Word8)
         <> toCBOR a

instance
  (Crypto crypto)
  => FromCBOR (CurItem crypto)
 where
  fromCBOR = do
    decodeWord >>= \case
      0 -> do
        a <- fromCBOR
        pure $ SH a
      1 -> do
        a <- fromCBOR
        pure $ TI a
      2 -> do
        a <- fromCBOR
        pure $ WD a
      3 -> do
        a <- fromCBOR
        pure $ DC a
      k -> invalidKey k

instance ToCBOR Rdmrs where
  toCBOR = mapToCBOR . getRMs
    where
      getRMs (Rdmrs rm) = rm

instance FromCBOR Rdmrs where
  fromCBOR = Rdmrs <$> mapFromCBOR

instance ToCBOR ScrTypes
 where
   toCBOR = \case
     InputTag -> toCBOR (0 :: Word8)
     ForgeTag -> toCBOR (1 :: Word8)
     CertTag  -> toCBOR (2 :: Word8)
     WdrlTag  -> toCBOR (3 :: Word8)

instance FromCBOR ScrTypes
 where
  fromCBOR = do
    decodeWord >>= \case
      0 -> pure InputTag
      1 -> pure ForgeTag
      2 -> pure CertTag
      3 -> pure WdrlTag
      k -> invalidKey k

instance
  (Crypto crypto)
  => ToCBOR (DCert crypto)
 where
   toCBOR = \case
           -- DCertDeleg
     DCertDeleg (RegKey (KeyHashObj h)) ->
           encodeListLen 2
           <> toCBOR (0 :: Word8)
           <> toCBOR h
     DCertDeleg (RegKey (ScriptHashObj h)) ->
           encodeListLen 2
           <> toCBOR (1 :: Word8)
           <> toCBOR h
     DCertDeleg (DeRegKey (KeyHashObj h)) ->
           encodeListLen 2
           <> toCBOR (2 :: Word8)
           <> toCBOR h
     DCertDeleg (DeRegKey (ScriptHashObj h)) ->
           encodeListLen 2
           <> toCBOR (3 :: Word8)
           <> toCBOR h
     DCertDeleg (Delegate (Delegation (KeyHashObj h) poolkh)) ->
           encodeListLen 3
           <> toCBOR (4 :: Word8)
           <> toCBOR h
           <> toCBOR poolkh
     DCertDeleg (Delegate (Delegation (ScriptHashObj h) poolkh)) ->
           encodeListLen 3
           <> toCBOR (5 :: Word8)
           <> toCBOR h
           <> toCBOR poolkh

           -- DCertPool
     DCertPool (RegPool poolParams) ->
           encodeListLen (1 + listLen poolParams)
           <> toCBOR (6 :: Word8)
           <> toCBORGroup poolParams
     DCertPool (RetirePool vk epoch) ->
           encodeListLen 3
           <> toCBOR (7 :: Word8)
           <> toCBOR vk
           <> toCBOR epoch

           -- DCertGenesis
     DCertGenesis (GenesisDelegate gk kh) ->
           encodeListLen 3
           <> toCBOR (8 :: Word8)
           <> toCBOR gk
           <> toCBOR kh

           -- DCertMIR
     DCertMir mir ->
           encodeListLen 2
           <> toCBOR (9 :: Word8)
           <> toCBOR mir

instance
  (Crypto crypto)
  => FromCBOR (DCert crypto)
 where
  fromCBOR = do
    n <- decodeListLen
    decodeWord >>= \case
      0 -> matchSize "RegKey" 2 n >> (DCertDeleg . RegKey . KeyHashObj) <$> fromCBOR
      1 -> matchSize "RegKey" 2 n >> (DCertDeleg . RegKey . ScriptHashObj) <$> fromCBOR
      2 -> matchSize "DeRegKey" 2 n >> (DCertDeleg . DeRegKey . KeyHashObj) <$> fromCBOR
      3 -> matchSize "DeRegKey" 2 n >> (DCertDeleg . DeRegKey . ScriptHashObj) <$> fromCBOR
      4 -> do
        matchSize "Delegate" 3 n
        a <- fromCBOR
        b <- fromCBOR
        pure $ DCertDeleg $ Delegate (Delegation (KeyHashObj a) b)
      5 -> do
        matchSize "Delegate" 3 n
        a <- fromCBOR
        b <- fromCBOR
        pure $ DCertDeleg $ Delegate (Delegation (ScriptHashObj a) b)
      6 -> do
        group <- fromCBORGroup
        matchSize "RegPool" (fromIntegral $ 1 + listLen group) n
        pure $ DCertPool $ RegPool group
      7 -> do
        matchSize "RetirePool" 3 n
        a <- fromCBOR
        b <- fromCBOR
        pure $ DCertPool $ RetirePool a (EpochNo b)
      8 -> do
        matchSize "GenesisDelegate" 3 n
        a <- fromCBOR
        b <- fromCBOR
        pure $ DCertGenesis $ GenesisDelegate a b
      9 -> matchSize "MIRCert" 2 n >> DCertMir <$> fromCBOR
      k -> invalidKey k

instance
  (Typeable crypto, Crypto crypto)
  => ToCBOR (TxIn crypto)
 where
  toCBOR (TxIn txId index isf) =
    encodeListLen 3
      <> toCBOR txId
      <> toCBOR (fromIntegral index :: Word64)
      <> toCBOR isf

instance (Crypto crypto) =>
  FromCBOR (TxIn crypto) where
  fromCBOR = do
    enforceSize "TxIn" 3
    a <- fromCBOR
    (b :: Word64) <- fromCBOR
    c <- fromCBOR
    pure $ TxIn a (fromInteger $ toInteger b) c

instance
  (Typeable crypto, Crypto crypto)
  => ToCBOR (UTxOIn crypto)
 where
  toCBOR (UTxOIn txId index) =
    encodeListLen 2
      <> toCBOR txId
      <> toCBOR (fromIntegral index :: Word64)

instance (Crypto crypto) =>
  FromCBOR (UTxOIn crypto) where
  fromCBOR = do
    enforceSize "UTxOIn" 2
    a <- fromCBOR
    (b :: Word64) <- fromCBOR
    pure $ UTxOIn a (fromInteger $ toInteger b)

instance
  (Typeable crypto, Crypto crypto)
  => ToCBOR (UTxOOut crypto)
 where
   toCBOR = \case
     UTxOOutND out s ->
       encodeListLen 3
         <> toCBOR (0 :: Word8)
         <> toCBOR out
         <> toCBOR s
     UTxOOutPT a b ->
       encodeListLen 3
         <> toCBOR (1 :: Word8)
         <> toCBOR a
         <> toCBOR b

instance
  (Typeable crypto, Crypto crypto)
  => ToCBOR (XOutND crypto)
 where
   toCBOR (XOutND addr v) =
       encodeListLen (listLen addr + 1)
         <> toCBORGroup addr
         <> toCBOR v

instance
  (Typeable crypto, Crypto crypto)
  => FromCBOR (XOutND crypto)
 where
  fromCBOR = do
    n <- decodeListLen
    addr <- fromCBORGroup
    v <- fromCBOR
    matchSize "OutND" ((fromIntegral . toInteger . listLen) addr + 1) n
    pure $ XOutND addr v

instance
  (Typeable crypto, Crypto crypto)
  => ToCBOR (OutND crypto)
 where
   toCBOR (OutND addr v) =
       encodeListLen (listLen addr + 1)
         <> toCBORGroup addr
         <> toCBOR v

instance
  (Typeable crypto, Crypto crypto)
  => FromCBOR (OutND crypto)
 where
  fromCBOR = do
    n <- decodeListLen
    addr <- fromCBORGroup
    v <- fromCBOR
    matchSize "OutND" ((fromIntegral . toInteger . listLen) addr + 1) n
    pure $ OutND addr v

instance
  (Typeable crypto, Crypto crypto)
  => FromCBOR (UTxOOut crypto)
 where
  fromCBOR = do
    decodeWord >>= \case
      0 -> do
        out <- fromCBOR
        s   <- fromCBOR
        pure $ UTxOOutND out s
      1 -> do
        a <- fromCBOR
        b <- fromCBOR
        pure $ UTxOOutPT a b
      k -> invalidKey k

instance
  (Typeable crypto, Crypto crypto)
  => ToCBOR (TxOut crypto)
 where
   toCBOR = \case
     TxOutND out ->
       encodeListLen 2
         <> toCBOR (0 :: Word8)
         <> toCBOR out
     TxOutPT a b ->
       encodeListLen 3
         <> toCBOR (1 :: Word8)
         <> toCBOR a
         <> toCBOR b

instance
  (Typeable crypto, Crypto crypto)
  => FromCBOR (TxOut crypto)
 where
  fromCBOR = do
    decodeWord >>= \case
      0 -> do
        out <- fromCBOR
        pure $ TxOutND out
      1 -> do
        a <- fromCBOR
        b <- fromCBOR
        pure $ TxOutPT a b
      k -> invalidKey k


instance
  (Typeable crypto, Crypto crypto)
  => ToCBOR (UTxOOutP crypto)
 where
  toCBOR (UTxOOutP addr v h) =
    encodeListLen (listLen addr + 2)
      <> toCBORGroup addr
      <> toCBOR v
      <> toCBOR h

instance (Crypto crypto) =>
  FromCBOR (UTxOOutP crypto) where
  fromCBOR = do
    n <- decodeListLen
    addr <- fromCBORGroup
    v <- fromCBOR
    h <- fromCBOR
    matchSize "UTxOOutP" ((fromIntegral . toInteger . listLen) addr + 1) n
    pure $ UTxOOutP addr v h

instance
  (Typeable crypto, Crypto crypto)
  => ToCBOR (TxOutP crypto)
 where
  toCBOR (TxOutP addr v h) =
    encodeListLen (listLen addr + 2)
      <> toCBORGroup addr
      <> toCBOR v
      <> toCBOR h

instance (Crypto crypto) =>
  FromCBOR (TxOutP crypto) where
  fromCBOR = do
    n <- decodeListLen
    addr <- fromCBORGroup
    v <- fromCBOR
    h <- fromCBOR
    matchSize "TxOutP" ((fromIntegral . toInteger . listLen) addr + 1) n
    pure $ TxOutP addr v h

instance
  Crypto crypto
  => ToCBOR (WitVKey crypto)
 where
  toCBOR (WitVKey vk sig) =
    encodeListLen 2
      <> toCBOR vk
      <> toCBOR sig

instance
  Crypto crypto
  => FromCBOR (WitVKey crypto)
 where
  fromCBOR = do
    enforceSize "WitVKey" 2
    a <- fromCBOR
    b <- fromCBOR
    pure $ WitVKey a b

--
-- data CBORWits crypto
--   = CBORWits
--       { _cborWitsVKeys   :: CborSeq (WitVKey crypto)
--       , _cborScripts :: CborSeq (Script crypto)
--       , _cborDats :: CborSeq Data
--       , _cborRdmrs :: CBORMap RdmrPtr Data
--       } deriving (Generic)
--
-- instance (Crypto crypto) =>
--   ToCBOR (CBORWits crypto) where
--   toCBOR ws =
--     let l = catMaybes $
--               [ encodeMapElement 0 $ _cborWitsVKeys ws
--               , encodeMapElement 1 $ _cborScripts ws
--               , encodeMapElement 2 $ _cborDats ws
--               , encodeMapElement 3 $ _cborRdmrs ws
--               ]
--         n = fromIntegral $ length l
--     in encodeMapLen n <> fold l
--     where
--       encodeMapElement ix x = if null x then Nothing else Just (encodeWord ix <> toCBOR x)
--
-- instance (Crypto crypto) =>
--   FromCBOR (CBORWits crypto) where
--   fromCBOR = do
--     mapParts <- decodeMapContents $
--       decodeWord >>= \case
--         0 -> fromCBOR >>= \x -> pure (\w -> w { _cborWitsVKeys  = x })
--         1 -> fromCBOR >>= \x -> pure (\w -> w { _cborScripts  = x })
--         2 -> fromCBOR >>= \x -> pure (\w -> w { _cborDats  = x })
--         3 -> fromCBOR >>= \x -> pure (\w -> w { _cborRdmrs  = x })
--         k -> invalidKey k
--     pure $ foldr ($) start mapParts
--     where
--       start = CBORWits
--          { _cborWitsVKeys = CborSeq Seq.empty
--          , _cborScripts   = CborSeq Seq.empty
--          , _cborDats      = CborSeq Seq.empty
--          , _cborRdmrs     = CBORMap Map.empty
--          }
--
instance
  Crypto crypto
  => FromCBOR (TxWitness crypto)
 where
  fromCBOR = do
    enforceSize "TxWitness" 4
    vkwts <- fromCBOR
    scrts <- fromCBOR
    dts <- fromCBOR
    rdmrs <- fromCBOR
    pure $ TxWitness vkwts scrts dts rdmrs

instance
  Crypto crypto
  => ToCBOR (TxWitness crypto)
 where
  toCBOR (TxWitness vkwts scrts dts rdmrs) =
    encodeListLen 4
      <> toCBOR vkwts
      <> toCBOR scrts
      <> toCBOR dts
      <> toCBOR rdmrs

instance
  (Crypto crypto)
  => ToCBOR (TxBody crypto)
 where
  toCBOR txbody =
    let l = catMaybes
          [ encodeMapElement 0 $ _inputs txbody
          , encodeMapElement 1 $ CborSeq $ StrictSeq.getSeq $ _outputs txbody
          , encodeMapElement 2 $ _txfee txbody
          , encodeMapElement 3 $ _fst txbody
          , encodeMapElement 4 $ _ttl txbody
          , encodeMapElementUnless null 5 $ CborSeq $ StrictSeq.getSeq $_certs txbody
          , encodeMapElementUnless (null . val) 6 $ _forge txbody
          , encodeMapElementUnless ((==) defaultUnits) 7 $ _exunits txbody -- TODO maybe type
          , encodeMapElementUnless (null . unWdrl) 8 $ _wdrls txbody
          , encodeMapElement 9 =<< strictMaybeToMaybe (_txUpdate txbody)
          , encodeMapElement 10 =<< strictMaybeToMaybe (_ppHash txbody)
          , encodeMapElement 11 =<< strictMaybeToMaybe (_rdmrsHash txbody)
          , encodeMapElement 12 =<< strictMaybeToMaybe (_mdHash txbody)
          ]
        n = fromIntegral $ length l
    in encodeMapLen n <> fold l
    where
      encodeMapElement ix x = Just (encodeWord ix <> toCBOR x)
      encodeMapElementUnless condition ix x =
        if condition x
          then Nothing
          else encodeMapElement ix x

instance
  (Crypto crypto)
  => FromCBOR (TxBody crypto)
  where
   fromCBOR = do
     mapParts <- decodeMapContents $
       decodeWord >>= \case
         0 -> fromCBOR                      >>= \x -> pure (0, \t -> t { _inputs   = x })
         1 -> (unwrapCborStrictSeq <$> fromCBOR)  >>= \x -> pure (1, \t -> t { _outputs  = x })
         2 -> fromCBOR                      >>= \x -> pure (2, \t -> t { _txfee    = x })
         3 -> fromCBOR                      >>= \x -> pure (3, \t -> t { _fst      = x })
         4 -> fromCBOR                      >>= \x -> pure (4, \t -> t { _ttl      = x })
         5 -> (unwrapCborStrictSeq <$> fromCBOR)  >>= \x -> pure (5, \t -> t { _certs    = x })
         6 -> fromCBOR                      >>= \x -> pure (6, \t -> t { _forge    = x })
         7 -> fromCBOR                      >>= \x -> pure (7, \t -> t { _exunits  = x })
         8 -> fromCBOR                      >>= \x -> pure (8, \t -> t { _wdrls    = x })
         9 -> fromCBOR                      >>= \x -> pure (9, \t -> t { _txUpdate = SJust x })
         10 -> fromCBOR                     >>= \x -> pure (10, \t -> t { _ppHash   = SJust x })
         11 -> fromCBOR                     >>= \x -> pure (11, \t -> t { _rdmrsHash= SJust x })
         12 -> fromCBOR                     >>= \x -> pure (12, \t -> t { _mdHash   = SJust x })
         k -> invalidKey k
     let requiredFields :: Map Int String
         requiredFields = Map.fromList $
           [ (0, "inputs")
           , (1, "outputs")
           , (2, "fee")
           , (3, "ttl")
           ]
         fields = fst <$> mapParts
         missingFields = Map.filterWithKey (\k _ -> notElem k fields) requiredFields
     unless (null missingFields)
       (fail $ "missing required transaction component(s): " <> show missingFields)
     pure $ foldr ($) basebody (snd <$> mapParts)
     where
       basebody = TxBody
          { _inputs   = Set.empty
          , _outputs  = StrictSeq.empty
          , _txfee    = Coin 0
          , _fst      = SlotNo 0
          , _ttl      = SlotNo 0
          , _certs    = StrictSeq.empty
          , _forge    = zeroV
          , _exunits  = defaultUnits
          , _wdrls    = Wdrl Map.empty
          , _txUpdate = SNothing
          , _ppHash   = SNothing
          , _rdmrsHash= SNothing
          , _mdHash   = SNothing
          }


instance (Typeable crypto, Crypto crypto)
  => ToCBORGroup (Credential crypto) where
  listLen _ = 2
  toCBORGroup = \case
    KeyHashObj     kh -> toCBOR (0 :: Word8) <> toCBOR kh
    ScriptHashObj  hs -> toCBOR (1 :: Word8) <> toCBOR hs

instance (Typeable crypto, Crypto crypto)
  => ToCBOR (GenesisCredential crypto)
  where toCBOR (GenesisCredential kh) =
          toCBOR kh

instance (Crypto crypto) =>
  FromCBOR (Credential crypto) where
  fromCBOR = do
    enforceSize "Credential" 2
    decodeWord >>= \case
      0 -> KeyHashObj <$> fromCBOR
      1 -> ScriptHashObj <$> fromCBOR
      k -> invalidKey k

instance
  (Typeable crypto, Crypto crypto)
  => ToCBORGroup (Addr crypto)
 where
  listLen (Addr _ (StakeRefBase _)) = 3
  listLen (Addr _ (StakeRefPtr p)) = 2 + listLen p
  listLen (Addr _ (StakeRefNull)) = 2
  listLen (AddrBootstrap  _) = 2

  toCBORGroup (Addr (KeyHashObj a) (StakeRefBase (KeyHashObj b))) =
    toCBOR (0 :: Word8) <> toCBOR a <> toCBOR b
  toCBORGroup (Addr (KeyHashObj a) (StakeRefBase (ScriptHashObj b))) =
    toCBOR (1 :: Word8) <> toCBOR a <> toCBOR b
  toCBORGroup (Addr (ScriptHashObj a) (StakeRefBase (KeyHashObj b))) =
    toCBOR (2 :: Word8) <> toCBOR a <> toCBOR b
  toCBORGroup (Addr (ScriptHashObj a) (StakeRefBase (ScriptHashObj b))) =
    toCBOR (3 :: Word8) <> toCBOR a <> toCBOR b
  toCBORGroup (Addr (KeyHashObj a) (StakeRefPtr pointer)) =
    toCBOR (4 :: Word8) <> toCBOR a <> toCBORGroup pointer
  toCBORGroup (Addr (ScriptHashObj a) (StakeRefPtr pointer)) =
    toCBOR (5 :: Word8) <> toCBOR a <> toCBORGroup pointer
  toCBORGroup (Addr (KeyHashObj a) StakeRefNull) =
    toCBOR (6 :: Word8) <> toCBOR a
  toCBORGroup (Addr (ScriptHashObj a) StakeRefNull) =
    toCBOR (7 :: Word8) <> toCBOR a
  toCBORGroup (AddrBootstrap a) =
    toCBOR (8 :: Word8) <> toCBOR a

instance (Crypto crypto) =>
  FromCBORGroup (Addr crypto) where
  fromCBORGroup = do
    decodeWord >>= \case
      0 -> do
        a <- fromCBOR
        b <- fromCBOR
        pure $ Addr (KeyHashObj a) (StakeRefBase (KeyHashObj b))
      1 -> do
        a <- fromCBOR
        b <- fromCBOR
        pure $ Addr (KeyHashObj a) (StakeRefBase (ScriptHashObj b))
      2 -> do
        a <- fromCBOR
        b <- fromCBOR
        pure $ Addr (ScriptHashObj a) (StakeRefBase (KeyHashObj b))
      3 -> do
        a <- fromCBOR
        b <- fromCBOR
        pure $ Addr (ScriptHashObj a) (StakeRefBase (ScriptHashObj b))
      4 -> do
        a <- fromCBOR
        x <- fromCBOR
        y <- fromCBOR
        z <- fromCBOR
        pure $ Addr (KeyHashObj a) (StakeRefPtr (Ptr x y z))
      5 -> do
        a <- fromCBOR
        x <- fromCBOR
        y <- fromCBOR
        z <- fromCBOR
        pure $ Addr (ScriptHashObj a) (StakeRefPtr (Ptr x y z))
      6 -> do
        a <- fromCBOR
        pure $ Addr (KeyHashObj a) StakeRefNull
      7 -> do
        a <- fromCBOR
        pure $ Addr (ScriptHashObj a) StakeRefNull
      8 -> do
        a <- fromCBOR
        pure $ AddrBootstrap (KeyHash a)
      k -> invalidKey k

instance ToCBORGroup Ptr where
  toCBORGroup (Ptr sl txIx certIx) =
         toCBOR sl
      <> toCBOR (fromInteger (toInteger txIx) :: Word)
      <> toCBOR (fromInteger (toInteger certIx) :: Word)
  listLen _ = 3

instance FromCBORGroup Ptr where
  fromCBORGroup = Ptr <$> fromCBOR <*> fromCBOR <*> fromCBOR

instance ToCBOR PoolMetaData
 where
  toCBOR (PoolMetaData u h) =
    encodeListLen 2
      <> toCBOR u
      <> toCBOR h

instance FromCBOR PoolMetaData
  where
  fromCBOR = do
    enforceSize "PoolMetaData" 2
    u <- fromCBOR
    h <- fromCBOR
    pure $ PoolMetaData u h

instance
  (Crypto crypto)
  => ToCBORGroup (PoolParams crypto)
 where
  toCBORGroup poolParams =
         toCBOR (_poolPubKey poolParams)
      <> toCBOR (_poolVrf poolParams)
      <> toCBOR (_poolPledge poolParams)
      <> toCBOR (_poolCost poolParams)
      <> toCBOR (_poolMargin poolParams)
      <> toCBOR (_poolRAcnt poolParams)
      <> toCBOR (_poolOwners poolParams)
      <> toCBOR (CborSeq (StrictSeq.getSeq (_poolRelays poolParams)))
      <> toCBOR (_poolMD poolParams)
  listLen _ = 9

instance
  (Crypto crypto)
  => FromCBORGroup (PoolParams crypto)
 where
  fromCBORGroup = do
    vk <- fromCBOR
    vrf <- fromCBOR
    pledge <- fromCBOR
    cost <- fromCBOR
    margin <- fromCBOR
    ra <- fromCBOR
    owners <- fromCBOR
    relays <- fromCBOR
    md <- fromCBOR
    pure $ PoolParams
            { _poolPubKey = vk
            , _poolVrf    = vrf
            , _poolPledge = pledge
            , _poolCost   = cost
            , _poolMargin = margin
            , _poolRAcnt  = ra
            , _poolOwners = owners
            , _poolRelays = unwrapCborStrictSeq relays
            , _poolMD     = md
            }

instance Relation (StakeCreds crypto) where
  type Domain (StakeCreds crypto) = Credential crypto
  type Range (StakeCreds crypto)  = SlotNo

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
