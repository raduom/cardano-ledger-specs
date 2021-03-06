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

import           Cardano.Binary (FromCBOR (fromCBOR), ToCBOR (toCBOR), decodeListLen, decodeWord,
                     encodeListLen, encodeWord, encodeWord8, matchSize)
import           Cardano.Crypto.Hash (hashWithSerialiser)
import           Cardano.Prelude (Generic, NoUnexpectedThunks (..))
import qualified Data.List as List (concat, concatMap, permutations)
import           Data.Word (Word8)
import           Shelley.Spec.Ledger.BaseTypes (invalidKey)
import           Shelley.Spec.Ledger.Crypto (Crypto (..), HASH)
import           Shelley.Spec.Ledger.Keys (AnyKeyHash, pattern AnyKeyHash, Hash)
import           Shelley.Spec.Ledger.Serialization (decodeList, encodeFoldable)


-- | Magic number representing the tag of the native multi-signature script
-- language. For each script language included, a new tag is chosen and the tag
-- is included in the script hash for a script.
nativeMultiSigTag :: Word8
nativeMultiSigTag = 0


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
       RequireSignature  !(AnyKeyHash crypto)

       -- | Require all the sub-terms to be satisfied.
     | RequireAllOf      ![MultiSig crypto]

       -- | Require any one of the sub-terms to be satisfied.
     | RequireAnyOf      ![MultiSig crypto]

       -- | Require M of the given sub-terms to be satisfied.
     | RequireMOf   !Int ![MultiSig crypto]
  deriving (Show, Eq, Ord, Generic)

instance NoUnexpectedThunks (MultiSig crypto)

newtype ScriptHash crypto =
  ScriptHash (Hash (HASH crypto) (Script crypto))
  deriving (Show, Eq, Ord, NoUnexpectedThunks)

data Script crypto = MultiSigScript (MultiSig crypto)
                     -- new languages go here
  deriving (Show, Eq, Ord, Generic)

instance NoUnexpectedThunks (Script crypto)

deriving instance Crypto crypto => ToCBOR (ScriptHash crypto)
deriving instance Crypto crypto => FromCBOR (ScriptHash crypto)


-- | Count nodes and leaves of multi signature script
countMSigNodes :: MultiSig crypto -> Int
countMSigNodes (RequireSignature _) = 1
countMSigNodes (RequireAllOf msigs) = 1 + sum (map countMSigNodes msigs)
countMSigNodes (RequireAnyOf msigs) = 1 + sum (map countMSigNodes msigs)
countMSigNodes (RequireMOf _ msigs) = 1 + sum (map countMSigNodes msigs)



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

instance (Crypto crypto) =>
  ToCBOR (MultiSig crypto) where
  toCBOR (RequireSignature hk) =
    encodeListLen 2 <> encodeWord 0 <> toCBOR hk
  toCBOR (RequireAllOf msigs) =
    encodeListLen 2 <> encodeWord 1 <> encodeFoldable msigs
  toCBOR (RequireAnyOf msigs) =
    encodeListLen 2 <> encodeWord 2 <> encodeFoldable msigs
  toCBOR (RequireMOf m msigs) =
    encodeListLen 3 <> encodeWord 3 <> toCBOR m <> encodeFoldable msigs

instance (Crypto crypto) =>
  FromCBOR (MultiSig crypto) where
  fromCBOR = do
    n <- decodeListLen
    decodeWord >>= \case
      0 -> matchSize "RequireSignature" 2 n >> (RequireSignature . AnyKeyHash) <$> fromCBOR
      1 -> matchSize "RequireAllOf" 2 n >> RequireAllOf <$> decodeList fromCBOR
      2 -> matchSize "RequireAnyOf" 2 n >> RequireAnyOf <$> decodeList fromCBOR
      3 -> do
        matchSize "RequireMOf" 3 n
        m     <- fromCBOR
        msigs <- decodeList fromCBOR
        pure $ RequireMOf m msigs
      k -> invalidKey k

instance (Crypto crypto) =>
  ToCBOR (Script crypto) where
  toCBOR (MultiSigScript msig) =
    toCBOR nativeMultiSigTag <> toCBOR msig

instance (Crypto crypto) =>
  FromCBOR (Script crypto) where
  fromCBOR = do
    decodeWord >>= \case
      0 -> MultiSigScript <$> fromCBOR
      k -> invalidKey k
