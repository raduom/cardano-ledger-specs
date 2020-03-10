{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Shelley.Spec.Ledger.Value
 where

import           Cardano.Binary (ToCBOR, FromCBOR, toCBOR, fromCBOR, enforceSize, encodeListLen)
import           Cardano.Prelude (NoUnexpectedThunks(..))
import           Shelley.Spec.Ledger.Coin (Coin (..))
import           GHC.Generics (Generic)
import           Data.Map.Strict (Map, elems, empty, unionWith, toList)
import           Cardano.Ledger.Shelley.Crypto
import           Data.ByteString.Char8 (ByteString)
import           Shelley.Spec.Ledger.Scripts


-- | Quantity
newtype Quantity = Quantity Integer
  deriving (Show, Eq, Generic, ToCBOR, FromCBOR, Ord, Integral, Num, Real, Enum, NoUnexpectedThunks)


-- | Value type
data Value crypto = Value
  {
    coi :: Coin
  , val :: Map (ScriptHash crypto) (Map ByteString Quantity)
  }
  deriving (Show, Eq, Generic)

instance NoUnexpectedThunks (Value crypto)

-- adding and subtracting values
instance Num (Value crypto) where
   (Value (Coin c1) v1) + (Value (Coin c2) v2) = Value (Coin (c1+c2)) (unionWith (unionWith (+)) v1 v2)
   (Value (Coin c1) v1) - (Value (Coin c2) v2) = Value (Coin (c1+c2)) (unionWith (unionWith (-)) v1 v2)


-- Values are compared as functions that are 0 almost everywhere
instance Ord (Value crypto) where
   (<=) (Value (Coin c1) v1) (Value (Coin c2) v2) =
     ((<=) c1 c2) && (and $ fmap ((<=) 0) (getQs $ (Value 0 v1) - (Value 0 v2)))

-- get the quantities in the tokens of a value term
getQs :: (Value crypto) -> [Quantity]
getQs (Value _ v) = fmap snd (concat $ fmap toList (elems v))

-- zero value
zeroV :: Value crypto
zeroV = Value (Coin 0) empty

-- CBOR

instance (Crypto crypto) =>
 ToCBOR (Value crypto)
 where
   toCBOR (Value c vm) =
     encodeListLen 2
       <> toCBOR c
       <> toCBOR vm

instance (Crypto crypto) =>
 FromCBOR (Value crypto)
 where
   fromCBOR = do
     enforceSize "Value" 2
     a <- fromCBOR
     b <- fromCBOR
     pure $ Value a b
