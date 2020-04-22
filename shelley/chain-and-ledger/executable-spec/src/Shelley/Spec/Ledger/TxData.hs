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

import           Data.Binary
import           Data.Bits (testBit, (.|.))
import           Data.ByteString (ByteString)
import           Data.Coerce (coerce)
import           Data.Foldable (fold)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Ord (comparing)
import           Data.Sequence.Strict (StrictSeq)
import qualified Data.Sequence.Strict as StrictSeq
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Typeable (Typeable)
import           Data.Word (Word8)
import           GHC.Generics (Generic)
import           Numeric.Natural (Natural)

import           Byron.Spec.Ledger.Core (Relation (..))
import           Shelley.Spec.Ledger.BaseTypes (StrictMaybe (..), Text64, UnitInterval, invalidKey,
                     maybeToStrictMaybe, strictMaybeToMaybe)
import           Shelley.Spec.Ledger.Coin (Coin (..))
import           Shelley.Spec.Ledger.Keys (AnyKeyHash, GenKeyHash, Hash, KeyHash, pattern KeyHash,
                     Sig, VKey, VerKeyVRF, hashAnyKey)
import           Shelley.Spec.Ledger.MetaData (MetaDataHash)
import           Shelley.Spec.Ledger.PParams (Update)
import           Shelley.Spec.Ledger.Slot (EpochNo (..), SlotNo (..))

import           Shelley.Spec.Ledger.Serialization (CBORGroup (..), CborSeq (..),
                     FromCBORGroup (..), ToCBORGroup (..), decodeMapContents, decodeNullMaybe,
                     decodeSet, encodeFoldable, encodeNullMaybe, mapFromCBOR, mapToCBOR,
                     unwrapCborStrictSeq)

import           Shelley.Spec.Ledger.Scripts

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

putAddr :: Word8 -> Addr crypto -> Put
putAddr netID (AddrBootstrap kh) = undefined -- defer to byron
putAddr netId (Addr pc sr) =
  let payCredBit = case pc of
          ScriptHashObj _ -> 2^4 :: Word8
          KeyHashObj _ -> 0
   in case sr of
        StakeRefBase sc -> do
          let stakeCredBit = case sc of
                      ScriptHashObj _ -> 2^5
                      KeyHashObj _ -> 0
              header = stakeCredBit .|. payCredBit .|. netId
          putWord8 header
          putCredential pc
          putCredential sc
        StakeRefPtr (Ptr slot txIx certIx) -> do
           let header = 2^6 .|. payCredBit .|. netId
           putWord8 header
           putCredential pc
           putSlot slot
           putVariableLengthNat txIx
           putVariableLengthNat certIx
        StakeRefNull -> do
           let header = 2^6 .|. 2^5 .|. payCredBit .|. netId
           putWord8 header
           putCredential pc

getAddr :: Get (Maybe Word8, Addr crypto)
getAddr = do
  netId <- get
  header <- get
  if testBit header 3
    then do
      ba <- getByron netId header
      pure (Nothing, ba)
    else do
      case (testBit header 2, testBit header 1, testBit header 0) of
        (False, False, False) -> do
          pc <- getKeyHash
          sc <- getKeyHash
          pure (Just netId, Addr (KeyHashObj pc) (StakeRefBase $ KeyHashObj sc))
        (False, False, True) -> do
          pc <- getScriptHash
          sc <- getKeyHash
          pure (Just netId, Addr (ScriptHashObj pc) (StakeRefBase $ KeyHashObj sc))
        (False, True, False) -> do
          pc <- getKeyHash
          sc <- getScriptHash
          pure (Just netId, Addr (ScriptHashObj pc) (StakeRefBase $ KeyHashObj sc))
        (False, True, True) -> do
          pc <- getScriptHash
          sc <- getScriptHash
          pure (Just netId, Addr (ScriptHashObj pc) (StakeRefBase $ KeyHashObj sc))
      


putCredential :: Credential crypto -> Put
putCredential = undefined

putSlot :: SlotNo -> Put
putSlot = undefined

putVariableLengthNat :: Natural -> Put
putVariableLengthNat = undefined

getKeyHash :: Get (KeyHash crypto)
getKeyHash = undefined

getScriptHash :: Get (ScriptHash crypto)
getScriptHash = undefined

getByron :: Word8 -> Word8 -> Get (Addr crypto)
getByron netId header = undefined


instance NoUnexpectedThunks (Addr crypto)

type Ix  = Natural

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


-- |A unique ID of a transaction, which is computable from the transaction.
newtype TxId crypto
  = TxId { _TxId :: Hash (HASH crypto) (TxBody crypto) }
  deriving (Show, Eq, Ord, NoUnexpectedThunks)

deriving instance Crypto crypto => ToCBOR (TxId crypto)
deriving instance Crypto crypto => FromCBOR (TxId crypto)

-- |The input of a UTxO.
data TxIn crypto
  = TxIn !(TxId crypto) !Natural -- TODO use our own Natural type
  deriving (Show, Eq, Generic, Ord)

instance NoUnexpectedThunks (TxIn crypto)

-- |The output of a UTxO.
data TxOut crypto
  = TxOut !(Addr crypto) !Coin
  deriving (Show, Eq, Generic, Ord)

instance NoUnexpectedThunks (TxOut crypto)

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
      , _wdrls    :: !(Wdrl crypto)
      , _txfee    :: !Coin
      , _ttl      :: !SlotNo
      , _txUpdate :: !(StrictMaybe (Update crypto))
      , _mdHash   :: !(StrictMaybe (MetaDataHash crypto))
      } deriving (Show, Eq, Generic)

instance NoUnexpectedThunks (TxBody crypto)

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

instance
  (Crypto crypto)
  => ToCBOR (DCert crypto)
 where
   toCBOR = \case
           -- DCertDeleg
     DCertDeleg (RegKey cred) ->
           encodeListLen 2
           <> toCBOR (0 :: Word8)
           <> toCBOR cred
     DCertDeleg (DeRegKey cred) ->
           encodeListLen 2
           <> toCBOR (1 :: Word8)
           <> toCBOR cred
     DCertDeleg (Delegate (Delegation cred poolkh)) ->
           encodeListLen 3
           <> toCBOR (2 :: Word8)
           <> toCBOR cred
           <> toCBOR poolkh

           -- DCertPool
     DCertPool (RegPool poolParams) ->
           encodeListLen (1 + listLen poolParams)
           <> toCBOR (3 :: Word8)
           <> toCBORGroup poolParams
     DCertPool (RetirePool vk epoch) ->
           encodeListLen 3
           <> toCBOR (4 :: Word8)
           <> toCBOR vk
           <> toCBOR epoch

           -- DCertGenesis
     DCertGenesis (GenesisDelegate gk kh) ->
           encodeListLen 3
           <> toCBOR (5 :: Word8)
           <> toCBOR gk
           <> toCBOR kh

           -- DCertMIR
     DCertMir mir ->
           encodeListLen 2
           <> toCBOR (6 :: Word8)
           <> toCBOR mir

instance
  (Crypto crypto)
  => FromCBOR (DCert crypto)
 where
  fromCBOR = do
    n <- decodeListLen
    decodeWord >>= \case
      0 -> matchSize "RegKey" 2 n >> (DCertDeleg . RegKey) <$> fromCBOR
      1 -> matchSize "DeRegKey" 2 n >> (DCertDeleg . DeRegKey) <$> fromCBOR
      2 -> do
        matchSize "Delegate" 3 n
        a <- fromCBOR
        b <- fromCBOR
        pure $ DCertDeleg $ Delegate (Delegation a b)
      3 -> do
        group <- fromCBORGroup
        matchSize "RegPool" (fromIntegral $ 1 + listLen group) n
        pure $ DCertPool $ RegPool group
      4 -> do
        matchSize "RetirePool" 3 n
        a <- fromCBOR
        b <- fromCBOR
        pure $ DCertPool $ RetirePool a (EpochNo b)
      5 -> do
        matchSize "GenesisDelegate" 3 n
        a <- fromCBOR
        b <- fromCBOR
        pure $ DCertGenesis $ GenesisDelegate a b
      6 -> matchSize "MIRCert" 2 n >> DCertMir <$> fromCBOR
      k -> invalidKey k

instance
  (Typeable crypto, Crypto crypto)
  => ToCBOR (TxIn crypto)
 where
  toCBOR (TxIn txId index) =
    encodeListLen 2
      <> toCBOR txId
      <> toCBOR (fromIntegral index :: Word64)

instance (Crypto crypto) =>
  FromCBOR (TxIn crypto) where
  fromCBOR = do
    enforceSize "TxIn" 2
    a <- fromCBOR
    (b :: Word64) <- fromCBOR
    pure $ TxIn a (fromInteger $ toInteger b)

instance
  (Typeable crypto, Crypto crypto)
  => ToCBOR (TxOut crypto)
 where
  toCBOR (TxOut addr coin) =
    encodeListLen (listLen addr + 1)
      <> toCBORGroup addr
      <> toCBOR coin

instance (Crypto crypto) =>
  FromCBOR (TxOut crypto) where
  fromCBOR = do
    n <- decodeListLen
    addr <- fromCBORGroup
    (b :: Word64) <- fromCBOR
    matchSize "TxOut" ((fromIntegral . toInteger . listLen) addr + 1) n
    pure $ TxOut addr (Coin $ toInteger b)

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

instance
  (Crypto crypto)
  => ToCBOR (TxBody crypto)
 where
  toCBOR txbody =
    let l = catMaybes
          [ encodeMapElement 0 $ Set.toList $ _inputs txbody
          , encodeMapElement 1 $ CborSeq $ StrictSeq.getSeq $ _outputs txbody
          , encodeMapElement 2 $ _txfee txbody
          , encodeMapElement 3 $ _ttl txbody
          , encodeMapElementUnless null 4 $ CborSeq $ StrictSeq.getSeq $ _certs txbody
          , encodeMapElementUnless (null . unWdrl) 5 $ _wdrls txbody
          , encodeMapElement 6 =<< strictMaybeToMaybe (_txUpdate txbody)
          , encodeMapElement 7 =<< strictMaybeToMaybe (_mdHash txbody)
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
         0 -> decodeSet fromCBOR                 >>= \x -> pure (0, \t -> t { _inputs   = x })
         1 -> (unwrapCborStrictSeq <$> fromCBOR) >>= \x -> pure (1, \t -> t { _outputs  = x })
         2 -> fromCBOR                           >>= \x -> pure (2, \t -> t { _txfee    = x })
         3 -> fromCBOR                           >>= \x -> pure (3, \t -> t { _ttl      = x })
         4 -> (unwrapCborStrictSeq <$> fromCBOR) >>= \x -> pure (4, \t -> t { _certs    = x })
         5 -> fromCBOR                           >>= \x -> pure (5, \t -> t { _wdrls    = x })
         6 -> fromCBOR                           >>= \x -> pure (6, \t -> t { _txUpdate = SJust x })
         7 -> fromCBOR                           >>= \x -> pure (7, \t -> t { _mdHash   = SJust x })
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
          , _ttl      = SlotNo 0
          , _certs    = StrictSeq.empty
          , _wdrls    = Wdrl Map.empty
          , _txUpdate = SNothing
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
      <> encodeFoldable (_poolOwners poolParams)
      <> toCBOR (CborSeq (StrictSeq.getSeq (_poolRelays poolParams)))
      <> encodeNullMaybe toCBOR (strictMaybeToMaybe (_poolMD poolParams))
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
    owners <- decodeSet fromCBOR
    relays <- fromCBOR
    md <- decodeNullMaybe fromCBOR
    pure $ PoolParams
            { _poolPubKey = vk
            , _poolVrf    = vrf
            , _poolPledge = pledge
            , _poolCost   = cost
            , _poolMargin = margin
            , _poolRAcnt  = ra
            , _poolOwners = owners
            , _poolRelays = unwrapCborStrictSeq relays
            , _poolMD     = maybeToStrictMaybe md
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
