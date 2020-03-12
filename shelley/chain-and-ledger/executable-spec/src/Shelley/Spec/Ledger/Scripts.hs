{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}

module Shelley.Spec.Ledger.Scripts
  where

<<<<<<< HEAD
import           Cardano.Binary (FromCBOR (fromCBOR), ToCBOR (toCBOR), decodeWord,
                     encodeListLen, encodeWord, encodeWord8, matchSize, decodeListLen)
import           Shelley.Spec.Ledger.Serialization (decodeList, encodeFoldable)
import           Cardano.Crypto.Hash (hashWithSerialiser)
import qualified Data.List as List (concat, concatMap, permutations)
=======
import           Cardano.Binary (ToCBOR, FromCBOR, toCBOR, fromCBOR, decodeWord,
                 encodeListLen, encodeWord, decodeListLen, matchSize)
>>>>>>> changes from branch 2
import           Cardano.Prelude (Generic, NoUnexpectedThunks(..))
import           Cardano.Ledger.Shelley.Crypto (Crypto(..), HASH)
import           Data.Word (Word8)
import           Shelley.Spec.Ledger.BaseTypes (invalidKey)
import           Shelley.Spec.Ledger.Keys (AnyKeyHash, pattern AnyKeyHash, Hash)

<<<<<<< HEAD
=======
import           Shelley.Spec.Ledger.CostModel

-- | Tag
data IsThing = Yes | Nope
  deriving (Show, Eq, Generic, Ord)

instance NoUnexpectedThunks IsThing

-- | Validation tag
newtype IsValidating = IsValidating IsThing
  deriving (Show, Eq, Generic, NoUnexpectedThunks, Ord, ToCBOR, FromCBOR)

-- | For-fee tag
newtype IsFee = IsFee IsThing
  deriving (Show, Eq, Generic, NoUnexpectedThunks, Ord, ToCBOR, FromCBOR)

-- | has datavalue tag
newtype HasDV = HasDV IsThing
  deriving (Show, Eq, Generic, NoUnexpectedThunks, Ord, ToCBOR, FromCBOR)

-- STAND-IN things!!
-- temp plc script! Use these from Plutus
-- TODO make this right type from Plutus
newtype ScriptPLC = ScriptPLC Integer
<<<<<<< HEAD
  deriving (Show, Eq, Generic, NoUnexpectedThunks, Ord, ToCBOR)
>>>>>>> changes from branch 2
=======
  deriving (Show, Eq, Generic, NoUnexpectedThunks, Ord, ToCBOR, FromCBOR)
>>>>>>> working on LedgerState

-- | Magic number representing the tag of the native multi-signature script
-- language. For each script language included, a new tag is chosen and the tag
-- is included in the script hash for a script.
nativeMultiSigTag :: Word8
nativeMultiSigTag = 0

<<<<<<< HEAD
=======
-- | Magic number representing the tag of the native multi-signature script
-- language. For each script language included, a new tag is chosen and the tag
-- is included in the script hash for a script.
plcV1 :: Word8
plcV1 = 1
>>>>>>> changes from branch 2

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
  ScriptHash (Hash (HASH crypto) (Script crypto))
  deriving (Show, Eq, Ord, NoUnexpectedThunks)

data Script crypto = MultiSigScript (MultiSig crypto)
<<<<<<< HEAD
                     -- new languages go here
=======
                     | PlutusScriptV1 ScriptPLC
>>>>>>> changes from branch 2
  deriving (Show, Eq, Ord, Generic)

instance NoUnexpectedThunks (Script crypto)

deriving instance Crypto crypto => ToCBOR (ScriptHash crypto)
deriving instance Crypto crypto => FromCBOR (ScriptHash crypto)

<<<<<<< HEAD
=======
newtype DataHash crypto = DataHash (Hash (HASH crypto) Data)
  deriving (Show, Eq, Generic, NoUnexpectedThunks, Ord)


deriving instance Crypto crypto => ToCBOR (DataHash crypto)
deriving instance Crypto crypto => FromCBOR (DataHash crypto)
>>>>>>> changes from branch 2

-- | Count nodes and leaves of multi signature script
countMSigNodes :: MultiSig crypto -> Int
countMSigNodes (RequireSignature _) = 1
countMSigNodes (RequireAllOf msigs) = 1 + sum (map countMSigNodes msigs)
countMSigNodes (RequireAnyOf msigs) = 1 + sum (map countMSigNodes msigs)
countMSigNodes (RequireMOf _ msigs) = 1 + sum (map countMSigNodes msigs)

<<<<<<< HEAD


-- | Hashes native multi-signature script, appending the 'nativeMultiSigTag' in
-- front and then calling the script CBOR function.
hashAnyScript
  :: Crypto crypto
  => Script crypto
  -> ScriptHash crypto
hashAnyScript (MultiSigScript msig) =
  ScriptHash $ hashWithSerialiser (\x -> encodeWord8 nativeMultiSigTag
                                          <> toCBOR x) (MultiSigScript msig)

-- | Get one possible combination of keys for multi signature script
getKeyCombination :: MultiSig crypto -> [AnyKeyHash crypto]

getKeyCombination (RequireSignature hk) = [hk]
getKeyCombination (RequireAllOf msigs) =
  List.concatMap getKeyCombination msigs
getKeyCombination (RequireAnyOf msigs) =
  case msigs of
    []  -> []
    x:_ -> getKeyCombination x
getKeyCombination (RequireMOf m msigs) =
  List.concatMap getKeyCombination (take m msigs)


-- | Get all valid combinations of keys for given multi signature. This is
-- mainly useful for testing.
getKeyCombinations :: MultiSig crypto -> [[AnyKeyHash crypto]]

getKeyCombinations (RequireSignature hk) = [[hk]]

getKeyCombinations (RequireAllOf msigs) = [List.concat $
  List.concatMap getKeyCombinations msigs]

getKeyCombinations (RequireAnyOf msigs) = List.concatMap getKeyCombinations msigs

getKeyCombinations (RequireMOf m msigs) =
  let perms = map (take m) $ List.permutations msigs in
    map (concat . List.concatMap getKeyCombinations) perms



-- CBOR

=======
-- | Use these from Plutus
-- TODO make this Plutus type
newtype Data = Data Integer
  deriving (Show, Eq, Generic, NoUnexpectedThunks, Ord, ToCBOR, FromCBOR)

-- | temporary validator always returns true and same amount of resources
runPLCScript :: CostMod -> ScriptPLC -> [Data] -> ExUnits -> (IsValidating, ExUnits)
runPLCScript _ _ _ _ = (IsValidating Yes, ExUnits 0 0)

-- CBOR


>>>>>>> changes from branch 2
instance (Crypto crypto) =>
  ToCBOR (MultiSig crypto) where
  toCBOR (RequireSignature hk) =
    encodeListLen 2 <> encodeWord 0 <> toCBOR hk
  toCBOR (RequireAllOf msigs) =
<<<<<<< HEAD
    encodeListLen 2 <> encodeWord 1 <> encodeFoldable msigs
  toCBOR (RequireAnyOf msigs) =
    encodeListLen 2 <> encodeWord 2 <> encodeFoldable msigs
  toCBOR (RequireMOf m msigs) =
    encodeListLen 3 <> encodeWord 3 <> toCBOR m <> encodeFoldable msigs
=======
    encodeListLen 2 <> encodeWord 1 <> toCBOR msigs
  toCBOR (RequireAnyOf msigs) =
    encodeListLen 2 <> encodeWord 2 <> toCBOR msigs
  toCBOR (RequireMOf m msigs) =
    encodeListLen 3 <> encodeWord 3 <> toCBOR m <> toCBOR msigs
>>>>>>> changes from branch 2

instance (Crypto crypto) =>
  FromCBOR (MultiSig crypto) where
  fromCBOR = do
    n <- decodeListLen
    decodeWord >>= \case
      0 -> matchSize "RequireSignature" 2 n >> (RequireSignature . AnyKeyHash) <$> fromCBOR
<<<<<<< HEAD
      1 -> matchSize "RequireAllOf" 2 n >> RequireAllOf <$> decodeList fromCBOR
      2 -> matchSize "RequireAnyOf" 2 n >> RequireAnyOf <$> decodeList fromCBOR
      3 -> do
        matchSize "RequireMOf" 3 n
        m     <- fromCBOR
        msigs <- decodeList fromCBOR
=======
      1 -> matchSize "RequireAllOf" 2 n >> RequireAllOf <$> fromCBOR
      2 -> matchSize "RequireAnyOf" 2 n >> RequireAnyOf <$> fromCBOR
      3 -> do
        matchSize "RequireMOf" 3 n
        m     <- fromCBOR
        msigs <- fromCBOR
>>>>>>> changes from branch 2
        pure $ RequireMOf m msigs
      k -> invalidKey k

instance (Crypto crypto) =>
  ToCBOR (Script crypto) where
  toCBOR (MultiSigScript msig) =
    toCBOR nativeMultiSigTag <> toCBOR msig
<<<<<<< HEAD
=======
  toCBOR (PlutusScriptV1 plc) =
    toCBOR plcV1 <> toCBOR plc

>>>>>>> changes from branch 2

instance (Crypto crypto) =>
  FromCBOR (Script crypto) where
  fromCBOR = do
    decodeWord >>= \case
      0 -> MultiSigScript <$> fromCBOR
      1 -> PlutusScriptV1 <$> fromCBOR
      k -> invalidKey k
<<<<<<< HEAD
=======

instance ToCBOR IsThing
 where
   toCBOR = \case
     Yes  -> toCBOR (0 :: Word8)
     Nope -> toCBOR (1 :: Word8)

instance FromCBOR IsThing
 where
  fromCBOR = do
    decodeWord >>= \case
      0 -> pure Yes
      1 -> pure Nope
      k -> invalidKey k
>>>>>>> changes from branch 2
