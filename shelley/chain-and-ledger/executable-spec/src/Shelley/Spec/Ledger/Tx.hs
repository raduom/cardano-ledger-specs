{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}


module Shelley.Spec.Ledger.Tx
  ( -- transaction
    Tx(..)
  , TxBody(..)
  , TxOut(..)
  , TxIn(..)
  , TxId(..)
  , txUpdate
  , inputs
  , outputs
  , certs
  , wdrls
  , txfee
  , ttl
  , body
  , metadata
  , txwits
  -- , witnessVKeySet
  -- , witnessMSigMap
    -- witness data
  , WitVKey(..)
  , MultiSignatureScript
  , validateScript
  , hashScript
  , txwitsScript
  , extractKeyHash
  , extractScriptHash
  , extractGenKeyHash
  , getKeyCombinations
  , getKeyCombination
  -- , txToCBORWits
  -- , cborWitsToTx
  )
where


import           Shelley.Spec.Ledger.Keys (AnyKeyHash, GenKeyHash, undiscriminateKeyHash, Hash, hash)

import           Cardano.Binary (FromCBOR (fromCBOR), ToCBOR (toCBOR), decodeWord,
                     encodeListLen, encodeWord, encodeMapLen, decodeListLenOf)
import           Cardano.Crypto.Hash (hashWithSerialiser)
import           Cardano.Ledger.Shelley.Crypto
import           Cardano.Prelude (NoUnexpectedThunks (..))
import qualified Data.List as List (concat, concatMap, permutations)
import           Data.Map.Strict (Map, insert, empty)
import qualified Data.Map.Strict as Map
import           Data.Maybe (mapMaybe)
import           Data.Set (Set)
import qualified Data.Set as Set
import           GHC.Generics (Generic)
import           Shelley.Spec.Ledger.MetaData (MetaData)
import           Shelley.Spec.Ledger.Scripts

import           Shelley.Spec.Ledger.Serialization (CborSeq (..), decodeMapContents)
import           Shelley.Spec.Ledger.TxData (Credential (..), TxBody (..),
                     TxId (..), TxIn (..), TxOut (..), WitVKey (..), TxWitness (..), certs, inputs,
                     outputs, ttl, txUpdate, txfee, wdrls, witKeyHash)
                     -- import           Shelley.Spec.Ledger.Serialization (CborSeq (..), decodeMapContents)
                     -- import           Shelley.Spec.Ledger.TxData (Credential (..), MultiSig (..), Script (..),
                     --                      ScriptHash (..), TxBody (..), TxId (..), TxIn (..), TxOut (..), WitVKey (..),
                     --                      nativeMultiSigTag, witKeyHash)

-- |A fully formed transaction.
data Tx crypto
  = Tx
      { _body           :: !(TxBody crypto)
      , _txwits         :: TxWitness crypto
      , _metadata       :: Maybe MetaData
      , _valtag         :: IsValidating
      } deriving (Show, Eq, Generic)

instance Crypto crypto => NoUnexpectedThunks (Tx crypto)



instance
  (Crypto crypto)
  => ToCBOR (Tx crypto)
 where
  toCBOR tx =
    encodeListLen 4
      <> toCBOR (_body tx)
      <> toCBOR (_txwits tx)
      <> toCBOR (_metadata tx)
      <> toCBOR (_valtag tx)

instance Crypto crypto => FromCBOR (Tx crypto) where
  fromCBOR = do
       enforceSize "Tx" 4
       bod <- fromCBOR
       wts <- fromCBOR
       md <- fromCBOR
       vt <- fromCBOR
       pure $ Tx bod wts md vt

-- | Typeclass for multis-signature script data types. Allows for script
-- validation and hashing.
class (Crypto crypto, ToCBOR a) =>
  MultiSignatureScript a crypto where
  validateScript :: a -> Tx crypto -> Bool
  hashScript :: a -> ScriptHash crypto

-- | instance of MultiSignatureScript type class
instance Crypto crypto =>
  MultiSignatureScript (MultiSig crypto) crypto where
  validateScript = validateNativeMultiSigScript
  hashScript = \x -> hashAnyScript (MultiSigScript x)

-- | Script evaluator for native multi-signature scheme. 'vhks' is the set of
-- key hashes that signed the transaction to be validated.
evalNativeMultiSigScript
  :: MultiSig crypto
  -> Set (AnyKeyHash crypto)
  -> Bool
evalNativeMultiSigScript (RequireSignature hk) vhks = Set.member hk vhks
evalNativeMultiSigScript (RequireAllOf msigs) vhks =
  all (`evalNativeMultiSigScript` vhks) msigs
evalNativeMultiSigScript (RequireAnyOf msigs) vhks =
  any (`evalNativeMultiSigScript` vhks) msigs
evalNativeMultiSigScript (RequireMOf m msigs) vhks =
  m <= sum [if evalNativeMultiSigScript msig vhks then 1 else 0 | msig <- msigs]

-- | Script validator for native multi-signature scheme.
validateNativeMultiSigScript
  :: (Crypto crypto)
  => MultiSig crypto
  -> Tx crypto
  -> Bool
validateNativeMultiSigScript msig tx =
  evalNativeMultiSigScript msig vhks
  where witsSet = _witnessVKeySet $ _txwits tx
        vhks    = Set.map witKeyHash witsSet



-- | script witness accessor function for Transactions
txwitsScript
  :: Crypto crypto
  => Tx crypto
  -> Map (ScriptHash crypto) (Script crypto)
txwitsScript tx = Set.foldl (\m a -> Map.insert (ScriptHash $ hash a) a m) Map.empty (_scripts $ _txwits tx)

extractKeyHash
  :: [Credential crypto]
  -> [AnyKeyHash crypto]
extractKeyHash =
  mapMaybe (\case
                KeyHashObj hk -> Just $ undiscriminateKeyHash hk
                _ -> Nothing)

extractScriptHash
  :: [Credential crypto]
  -> [ScriptHash crypto]
extractScriptHash =
  mapMaybe (\case
                ScriptHashObj hk -> Just hk
                _ -> Nothing)

extractGenKeyHash
  :: [GenKeyHash crypto]
  -> [AnyKeyHash crypto]
extractGenKeyHash = map undiscriminateKeyHash
