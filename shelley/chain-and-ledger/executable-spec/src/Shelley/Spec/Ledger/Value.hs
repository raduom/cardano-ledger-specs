{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

module Shelley.Spec.Ledger.Value
 where

import           Cardano.Binary (ToCBOR, FromCBOR, toCBOR, fromCBOR, enforceSize, encodeListLen,
                  decodeWord)
import           Cardano.Prelude (NoUnexpectedThunks(..))

import           Shelley.Spec.Ledger.BaseTypes (invalidKey)
import           Shelley.Spec.Ledger.Coin (Coin (..))
import           GHC.Generics (Generic)
import           Data.Word (Word8)
import           Cardano.Crypto.Hash (Hash, hash)
import           Data.Map.Strict (Map, elems, empty, unionWith, toList, singleton, filterWithKey, keys)
import           Cardano.Ledger.Shelley.Crypto
import           Data.ByteString.Char8 (ByteString, pack)
import           Shelley.Spec.Ledger.Scripts


-- | Quantity
newtype Quantity = Quantity Integer
  deriving (Show, Eq, Generic, ToCBOR, FromCBOR, Ord, Integral, Num, Real, Enum, NoUnexpectedThunks)


-- | Value type
data Value crypto = Value
  { val :: Map (ScriptHash crypto) (Map ByteString Quantity) }
  deriving (Show, Eq, Generic)

instance NoUnexpectedThunks (Value crypto)

-- | compact representation of Value
data CompactValue crypto = AdaOnly Coin | MixValue (Value crypto)
  deriving (Show, Eq, Generic, Ord)

instance NoUnexpectedThunks (CompactValue crypto)

-- adding and subtracting values
instance Num (Value crypto) where
   (Value v1) + (Value v2) = Value (unionWith (unionWith (+)) v1 v2)
   (Value v1) - (Value v2) = Value (unionWith (unionWith (-)) v1 v2)


-- Values are compared as functions that are 0 almost everywhere
instance Ord (Value crypto) where
   (<=) (Value v1) (Value v2) =
     and $ fmap ((<=) 0) (getQs $ (Value v1) - (Value v2))

-- get the quantities in the tokens of a value term
getQs :: (Value crypto) -> [Quantity]
getQs (Value v) = fmap snd (concat $ fmap toList (elems v))

-- zero value
zeroV :: Value crypto
zeroV = Value empty

-- | make a value out of a coin
coinToValue :: Crypto crypto => Coin -> Value crypto
coinToValue (Coin c) = Value $ singleton adaID (singleton adaToken (Quantity c))

-- | make a value out of a coin
getAdaAmount :: Crypto crypto => Value crypto -> Coin
getAdaAmount (Value v) = Coin $ c
  where
    Quantity c = foldl (+) (Quantity 0) (getQs $ Value $ filterWithKey (\k _ -> k == adaID) v)

-- | currency ID of Ada
-- TODO use the right script here
adaID :: Crypto crypto => ScriptHash crypto
adaID = ScriptHash $ hash $ PlutusScriptV1 (ScriptPLC 0)

-- | token of Ada
adaToken :: ByteString
adaToken = pack "Ada"

valueToCompactValue :: Crypto crypto => Value crypto -> CompactValue crypto
valueToCompactValue (Value v)
  | keys v == [adaID] = AdaOnly $ getAdaAmount $ Value v
  | otherwise                                 = MixValue $ Value v

compactValueToValue :: Crypto crypto => CompactValue crypto -> Value crypto
compactValueToValue (AdaOnly c)  = coinToValue c
compactValueToValue (MixValue v) = v

-- CBOR

instance
  (Crypto crypto)
  => ToCBOR (CompactValue crypto)
 where
   toCBOR = \case
     AdaOnly c ->
           encodeListLen 2
           <> toCBOR (0 :: Word8)
           <> toCBOR c
     MixValue (Value v) ->
           encodeListLen 2
           <> toCBOR (1 :: Word8)
           <> toCBOR v

instance
  (Crypto crypto)
  => FromCBOR (CompactValue crypto)
 where
  fromCBOR = do
    decodeWord >>= \case
      0 -> do
        c <- fromCBOR
        pure $ AdaOnly c
      1 -> do
        v <- fromCBOR
        pure $ MixValue $ Value v
      k -> invalidKey k


instance
  (Crypto crypto)
  => ToCBOR (Value crypto)
 where
   toCBOR = (\case
     AdaOnly c ->
           encodeListLen 2
           <> toCBOR (0 :: Word8)
           <> toCBOR c
     MixValue (Value v) ->
           encodeListLen 2
           <> toCBOR (1 :: Word8)
           <> toCBOR v) . valueToCompactValue

instance
  (Crypto crypto)
  => FromCBOR (Value crypto)
 where
  fromCBOR = do
    decodeWord >>= \case
      0 -> do
        c <- fromCBOR
        pure $ compactValueToValue $ AdaOnly c
      1 -> do
        v <- fromCBOR
        pure $ compactValueToValue $ MixValue $ Value v
      k -> invalidKey k
