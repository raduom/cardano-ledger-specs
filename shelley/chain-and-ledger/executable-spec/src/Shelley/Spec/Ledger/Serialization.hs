{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}

module Shelley.Spec.Ledger.Serialization
  ( ToCBORGroup (..)
  , FromCBORGroup (..)
  , CBORGroup (..)
  , CborSeq (..)
  , decodeList
  , decodeMapContents
  , encodeFoldable
  , groupRecord
  , rationalToCBOR
  , rationalFromCBOR
  , mapToCBOR
  , mapFromCBOR
  -- Annotated Decoding
  , AnnotatedDecoder (..)
  , withAnnotationSlice'
  , FromCBORAnnotated (..)
  , decodeAnnotated
  , withAnnotationSlice
  , fromCBOREmptyAnnotation
  , decodeWrapped
  )
where

import Prelude ()
import           Cardano.Prelude

import           Cardano.Binary (Decoder, DecoderError (..), Encoding, FromCBOR (..), ToCBOR (..),
                     decodeBreakOr, decodeListLenOrIndef, decodeMapLenOrIndef, decodeTag,
                     encodeBreak, encodeListLen, encodeListLenIndef, encodeMapLen,
                     encodeMapLenIndef, encodeTag, matchSize)
import           Control.Monad (replicateM, unless, void)
import           Data.Foldable (foldl')
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Ratio (Rational, denominator, numerator, (%))
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import qualified Data.ByteString.Lazy as BSL
import Codec.CBOR.Read (ByteOffset)
import Cardano.Binary (decodeFullDecoder, decodeWithByteSpan)

class Typeable a => ToCBORGroup a where
  toCBORGroup :: a -> Encoding
  listLen     :: a -> Word

newtype CBORGroup a = CBORGroup a

instance ToCBORGroup a => ToCBOR (CBORGroup a) where
  toCBOR (CBORGroup x) = encodeListLen (listLen x) <> toCBORGroup x

class Typeable a => FromCBORGroup a where
  fromCBORGroup :: Decoder s a

instance (FromCBORGroup a, ToCBORGroup a) => FromCBOR (CBORGroup a) where
  fromCBOR = CBORGroup <$> groupRecord

decodeRecord :: (a -> Int) -> Decoder s a -> Decoder s a
decodeRecord getRecordSize decode = do
  lenOrIndef <- decodeListLenOrIndef
  x <- decode
  case lenOrIndef of
    Just n -> matchSize "CBORGroup" (getRecordSize x) n
    Nothing -> void decodeBreakOr -- TODO: make this give better errors
  pure x

groupRecord :: forall a s. (ToCBORGroup a, FromCBORGroup a) => Decoder s a
groupRecord = decodeRecord (fromIntegral . toInteger . listLen) fromCBORGroup

mapToCBOR :: (ToCBOR a, ToCBOR b) => Map a b -> Encoding
mapToCBOR m =
    let l = fromIntegral $ Map.size m
        contents = Map.foldMapWithKey (\k v -> toCBOR k <> toCBOR v) m
    in
    if l <= 23
    then encodeMapLen l <> contents
    else encodeMapLenIndef <> contents <> encodeBreak

mapFromCBOR :: (Ord a, FromCBOR a, FromCBOR b) => Decoder s (Map a b)
mapFromCBOR = Map.fromList
    <$> decodeMapContents decodePair
    where
    decodePair = (,) <$> fromCBOR <*> fromCBOR

newtype CborSeq a = CborSeq { unwrapCborSeq :: Seq a }
  deriving Foldable

instance ToCBOR a => ToCBOR (CborSeq a) where
  toCBOR (CborSeq xs) =
    let l = fromIntegral $ Seq.length xs
        contents = foldMap toCBOR xs
    in wrapCBORArray l contents

instance FromCBOR a => FromCBOR (CborSeq a) where
  fromCBOR = CborSeq . Seq.fromList <$> decodeList fromCBOR

encodeFoldable :: (ToCBOR a, Foldable f) => f a -> Encoding
encodeFoldable xs = wrapCBORArray len contents
  where
    (len, contents) = foldl' go (0, mempty) xs
    go (!l, !enc) next = (l+1,enc <> toCBOR next)

wrapCBORArray :: Word -> Encoding -> Encoding
wrapCBORArray len contents =
  if len <= 23
    then encodeListLen len <> contents
    else encodeListLenIndef <> contents <> encodeBreak


decodeList :: Decoder s a -> Decoder s [a]
decodeList = decodeCollection decodeListLenOrIndef

decodeMapContents :: Decoder s a -> Decoder s [a]
decodeMapContents = decodeCollection decodeMapLenOrIndef

decodeCollection :: Decoder s (Maybe Int) -> Decoder s a -> Decoder s [a]
decodeCollection lenOrIndef el = snd <$> decodeCollectionWithLen lenOrIndef el

decodeCollectionWithLen
  :: Decoder s (Maybe Int)
  -> Decoder s a
  -> Decoder s (Int,[a])
decodeCollectionWithLen lenOrIndef el = do
  lenOrIndef >>= \case
    Just len -> (,) len <$> replicateM len el
    Nothing -> loop (0,[]) (not <$> decodeBreakOr) el
  where
  loop (n,acc) condition action = condition >>= \case
      False -> pure (n,acc)
      True -> action >>= \v -> loop (n+1, (v:acc)) condition action

rationalToCBOR :: Rational -> Encoding
rationalToCBOR r = encodeTag 30
  <> encodeListLen 2 <> toCBOR (numerator r) <> toCBOR (denominator r)

rationalFromCBOR :: Decoder s Rational
rationalFromCBOR = do
    t <- decodeTag
    unless (t == 30) $ cborError $ DecoderErrorCustom "rational" "expected tag 30"
    (numInts, ints) <- decodeCollectionWithLen (decodeListLenOrIndef) fromCBOR
    case ints of
      n:d:[] -> pure $ n % d
      _ -> cborError $ DecoderErrorSizeMismatch "rational" 2 numInts

-------------------------------------------------------------------------
-- Annotated Decoder
-------------------------------------------------------------------------

-- | An AnnotatedDecoder produces a value which needs a reference to the
-- original ByteString to be constructed. For example, consider
--
-- `data Foo = Foo Int ByteString`
--
-- where the ByteString is expected to be the serialized form of Foo.
--
-- The pattern `AnnotatedDecoder` takes care that the bytes provided are the
-- correct ones.
newtype AnnotatedDecoder s a
  = AnnotatedDecoder { unwrapAnn :: (Decoder s (LByteString -> a)) }
  deriving (Functor)

instance Applicative (AnnotatedDecoder s) where
  pure x = AnnotatedDecoder $ const <$> pure x
  (AnnotatedDecoder a) <*> (AnnotatedDecoder b) =
    AnnotatedDecoder $ (<*>) <$> a <*> b

decodeAnnotated :: forall a. (Typeable a , FromCBORAnnotated a)
  => LByteString
  -> Either DecoderError a
decodeAnnotated = decodeAnnotatedDecoder (show . typeRep $ Proxy @a) fromCBORAnnotated

decodeAnnotatedDecoder :: Text -> (forall s. AnnotatedDecoder s a) -> LByteString -> Either DecoderError a
decodeAnnotatedDecoder label' decoder bytes =
  (\x -> x bytes) <$> decodeFullDecoder label' (unwrapAnn decoder) bytes

withSlice :: AnnotatedDecoder s (LByteString -> a) -> AnnotatedDecoder s a
withSlice (AnnotatedDecoder dec) = AnnotatedDecoder $ do
  (k, start, end) <- decodeWithByteSpan dec
  return $ \bytes -> k bytes (sliceOffsets start end bytes)
  where
  sliceOffsets :: ByteOffset -> ByteOffset -> LByteString -> LByteString
  sliceOffsets start end = (BSL.take (end - start) . BSL.drop start)

withSlice' :: forall s a. AnnotatedDecoder s (ByteString -> a) -> AnnotatedDecoder s a
withSlice' = withSlice . fmap (. BSL.toStrict)

-- | Wrap a plain decoder into an annotated one.
liftAnn :: Decoder s a -> AnnotatedDecoder s a
liftAnn dec = AnnotatedDecoder $ const <$> dec

-- | Wrap a plain decoder into an annotated one that populates the ByteString with a slice.
withAnnotationSlice :: forall s a. Decoder s (LByteString -> a) -> AnnotatedDecoder s a
withAnnotationSlice = withSlice . liftAnn

-- | Strict version of withAnnotationSlice
withAnnotationSlice' :: forall s a. Decoder s (ByteString -> a) -> AnnotatedDecoder s a
withAnnotationSlice' = withSlice' . liftAnn

class FromCBORAnnotated a where
  fromCBORAnnotated :: forall s. AnnotatedDecoder s a

fromCBOREmptyAnnotation :: FromCBORAnnotated a => Decoder s a
fromCBOREmptyAnnotation = (\x -> x mempty) <$> unwrapAnn fromCBORAnnotated

-------------------------------------------------------------------------
-- Wrapped Decoder
-------------------------------------------------------------------------

-- | Wrap both annotated and plain decoders
data WrappedDecoder a =
    Ann !(forall s. AnnotatedDecoder s a)
  | Plain !(forall s. Decoder s a)
  deriving Functor
  deriving NoUnexpectedThunks via
     OnlyCheckIsWHNF "WrappedDecoder" (WrappedDecoder a)

decodeWrapped
  :: forall a
  . (Typeable a)
  => WrappedDecoder a
  -> BSL.ByteString
  -> Either DecoderError a
decodeWrapped (Ann ad) = decodeAnnotatedDecoder (show . typeRep $ Proxy @a) ad
decodeWrapped (Plain d) = decodeFullDecoder (show . typeRep $ Proxy @a) d

