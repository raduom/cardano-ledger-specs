{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}

module Shelley.Spec.Ledger.MetaData
  ( MetaDatum (..)
  , MetaData (..)
  , MetaDataHash (..)
  , hashMetaData
) where

import           Cardano.Binary (DecoderError (..), FromCBOR (fromCBOR), ToCBOR (toCBOR))
import           Cardano.Crypto.Hash (Hash, hash)
import           Cardano.Prelude (NoUnexpectedThunks (..), Word64, cborError)
import           Data.Bifunctor (bimap)
import           Data.Bitraversable (bitraverse)
import           Data.ByteString as B
import           Data.ByteString.Lazy as BL
import           Data.Map.Strict (Map)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import           Shelley.Spec.Ledger.Crypto (Crypto, HASH)

import qualified Codec.CBOR.Term as CBOR

import           GHC.Generics (Generic)
import           Shelley.Spec.Ledger.Serialization (mapFromCBOR, mapToCBOR)

-- | A generic metadatum type.
--
-- TODO make strict
data MetaDatum
    = Map [(MetaDatum, MetaDatum)]
    | List [MetaDatum]
    | I Integer
    | B B.ByteString
    | S T.Text
    deriving stock (Show, Eq, Ord, Generic)

instance NoUnexpectedThunks MetaDatum

newtype MetaData = MetaData (Map Word64 MetaDatum)
  deriving (Eq, Show, Generic, NoUnexpectedThunks)

instance ToCBOR MetaData where
  toCBOR (MetaData m) = mapToCBOR m

instance FromCBOR MetaData where
  fromCBOR = MetaData <$> mapFromCBOR

type CBORToDataError = String

{- Note [Permissive decoding]
We're using a canonical representation of lists, maps, bytes, and integers. However,
the CBOR library does not guarantee that a TInteger gets encoded as a big integer,
so we can't rely on getting back our canonical version when we decode (see
https://github.com/well-typed/cborg/issues/222). So we need to be permissive
when we decode.
-}

fromTerm :: CBOR.Term -> Either CBORToDataError MetaDatum
fromTerm t =
  case t of
    CBOR.TInt i -> Right $ I (fromIntegral i)
    CBOR.TInteger i -> Right $ I i
    CBOR.TBytes b -> Right $ B b
    CBOR.TBytesI b -> Right $ B (BL.toStrict b)
    CBOR.TString  s -> Right $ S s
    CBOR.TStringI s -> Right $ S (TL.toStrict s)
    CBOR.TMap m -> Map <$> traverse (bitraverse fromTerm fromTerm) m
    CBOR.TMapI m -> Map <$> traverse (bitraverse fromTerm fromTerm) m
    CBOR.TList l -> List <$> traverse fromTerm l
    CBOR.TListI l -> List <$> traverse fromTerm l
    _ -> Left $ "Unsupported CBOR term: " ++ show t

toTerm :: MetaDatum -> CBOR.Term
toTerm = \case
    I i -> CBOR.TInteger i
    B b -> CBOR.TBytes b
    S s -> CBOR.TString s
    Map entries -> CBOR.TMap (fmap (bimap toTerm toTerm) entries)
    List ts -> CBOR.TList (fmap toTerm ts)

instance ToCBOR MetaDatum
 where
   toCBOR = CBOR.encodeTerm . toTerm

instance FromCBOR MetaDatum
 where
   fromCBOR = do
     t <- CBOR.decodeTerm
     case fromTerm t of
       Right d -> pure d
       Left e   -> (cborError . DecoderErrorCustom "metadata" . T.pack) e

newtype MetaDataHash crypto
  = MetaDataHash { unsafeMetaDataHash :: Hash (HASH crypto) MetaData }
  deriving (Show, Eq, Ord, NoUnexpectedThunks)

deriving instance Crypto crypto => ToCBOR (MetaDataHash crypto)
deriving instance Crypto crypto => FromCBOR (MetaDataHash crypto)

hashMetaData
  :: Crypto crypto
  => MetaData
  -> MetaDataHash crypto
hashMetaData = MetaDataHash . hash
