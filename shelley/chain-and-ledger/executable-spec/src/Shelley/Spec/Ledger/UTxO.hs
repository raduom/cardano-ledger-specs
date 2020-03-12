{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}

-- for the Relation instance
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-|
Module      : UTxO
Description : Simple UTxO Ledger

This module defines the types and functions for a simple UTxO Ledger
as specified in /A Simplified Formal Specification of a UTxO Ledger/.
-}

module Shelley.Spec.Ledger.UTxO
  (
  -- * Primitives
    UTxO(..)
  -- * Functions
  , txid
  , txins
  , txinLookup
  , txouts
  , txup
  , balance
  , totalDeposits
  , makeWitnessVKey
  , makeWitnessesVKey
  , makeWitnessesFromScriptKeys
  , verifyWitVKey
  , scriptsNeeded
  , txinsScript
  , mkUTxOout
  ) where

import           Cardano.Binary (FromCBOR (..), ToCBOR (..))
import           Cardano.Prelude (NoUnexpectedThunks (..))
import           Data.Foldable (toList)
import           Data.Map.Strict (Map, keys)
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
import           Data.Set (Set, map)
import qualified Data.Set as Set

import           Cardano.Ledger.Shelley.Crypto
import           Ledger.Core (Relation (..))
import           Shelley.Spec.Ledger.Coin (Coin (..))
import           Shelley.Spec.Ledger.Keys (AnyKeyHash, KeyDiscriminator (..), KeyPair, Signable,
                     hash, sKey, sign, vKey, verify)
import           Shelley.Spec.Ledger.PParams (PParams (..))
import           Shelley.Spec.Ledger.Tx (Tx (..))
import           Shelley.Spec.Ledger.TxData (Addr (..), Credential (..), pattern DeRegKey,
                     pattern Delegate, pattern Delegation, PoolCert (..), PoolParams (..),
                     TxBody (..), TxId (..), TxIn (..), Wdrl (..), UTxOOut(..),
                     WitVKey (..), getRwdCred, getAddress, getValue, getAddressTx, getValueTx)

-- .                     TxBody (..), TxId (..), TxIn (..), TxOut (..), Wdrl (..),
--                      WitVKey (..), getRwdCred)
-- =======
--                      pattern Delegate, pattern Delegation, PoolCert (..), TxBody (..),
--                      UTxOIn (..), UTxOOut (..), OutND (..), TxOutP (..), UTxOOutP (..), XOutND (..),
--                      TxId (..), TxIn (..), TxOut (..), Wdrl (..), WitVKey (..), getRwdCred, utxoref,
--                      outputs, poolPubKey, txUpdate, getValue, getAddress)

import           Shelley.Spec.Ledger.Updates (Update)
import           Shelley.Spec.Ledger.Slot (SlotNo (..))

import           Data.Coerce (coerce)
import           Shelley.Spec.Ledger.Delegation.Certificates (DCert (..), StakePools (..), dvalue,
                     requiresVKeyWitness)
import           Shelley.Spec.Ledger.Scripts
import           Shelley.Spec.Ledger.Value

import           Shelley.Spec.Ledger.Scripts
import           Shelley.Spec.Ledger.Value

-- |The unspent transaction outputs.
newtype UTxO crypto
  = UTxO (Map (UTxOIn crypto) (UTxOOut crypto))
  deriving (Show, Eq, Ord, ToCBOR, FromCBOR, NoUnexpectedThunks)

instance Relation (UTxO crypto) where
  type Domain (UTxO crypto) = UTxOIn crypto
  type Range (UTxO crypto)  = UTxOOut crypto

  singleton k v = UTxO $ Map.singleton k v

  dom (UTxO utxo) = dom utxo

  range (UTxO utxo) = range utxo

  s ◁ (UTxO utxo) = UTxO $ s ◁ utxo

  s ⋪ (UTxO utxo) = UTxO $ s ⋪ utxo

  (UTxO utxo) ▷ s = UTxO $ utxo ▷ s

  (UTxO utxo) ⋫ s = UTxO $ utxo ⋫ s

  (UTxO a) ∪ (UTxO b) = UTxO $ a ∪ b

  (UTxO a) ⨃ b = UTxO $ a ⨃ b

  vmax <=◁ (UTxO utxo) = UTxO $ vmax <=◁ utxo

  (UTxO utxo) ▷<= vmax = UTxO $ utxo ▷<= vmax

  (UTxO utxo) ▷>= vmin = UTxO $ utxo ▷>= vmin

  size (UTxO utxo) = size utxo

-- |Compute the id of a transaction.
txid
  :: Crypto crypto
  => TxBody crypto
  -> TxId crypto
txid = TxId . hash

-- |Compute the UTxO inputs from inputs of a transaction.
txins
  :: TxBody crypto
  -> Set (UTxOIn crypto)
txins txb = Set.map utxoref (_inputs txb)

-- | makes a UTxO output from a Tx output
mkUTxOout :: Crypto crypto
  => SlotNo
  -> TxOut crypto
  -> UTxOOut crypto
mkUTxOout s (TxOutND (OutND a v)) = UTxOOutND (XOutND a (valueToCompactValue v)) s
mkUTxOout s (TxOutPT (TxOutP a v dh) _) = UTxOOutPT (UTxOOutP a (valueToCompactValue v) dh) s


-- |Compute the transaction outputs of a transaction.
txouts
  :: Crypto crypto
  => SlotNo
  -> TxBody crypto
  -> UTxO crypto
txouts s tx = UTxO $
  Map.fromList [(UTxOIn transId idx, mkUTxOout s out) | (out, idx) <- zip (toList $ tx ^. outputs) [0..]]
  where
    transId = txid tx

-- |Lookup a txin for a given UTxO collection
txinLookup
  :: TxIn crypto
  -> UTxO crypto
  -> Maybe (UTxOOut crypto)
txinLookup txin (UTxO utxo') = Map.lookup (utxoref txin) utxo'

-- |Verify a transaction body witness
verifyWitVKey
  :: ( Crypto crypto
     , Signable (DSIGN crypto) (TxBody crypto)
     )
  => TxBody crypto
  -> WitVKey crypto
  -> Bool
verifyWitVKey tx (WitVKey vkey sig) = verify vkey tx sig

-- |Create a witness for transaction
makeWitnessVKey
  :: ( Crypto crypto
     , Signable (DSIGN crypto) (TxBody crypto)
     )
  => TxBody crypto
  -> KeyPair a crypto
  -> WitVKey crypto
makeWitnessVKey tx vkeys = WitVKey (coerce $ vKey vkeys) (sign (sKey vkeys) tx)

-- |Create witnesses for transaction
makeWitnessesVKey
  :: ( Crypto crypto
     , Signable (DSIGN crypto) (TxBody crypto)
     )
  => TxBody crypto
  -> [KeyPair a crypto]
  -> Set (WitVKey crypto)
makeWitnessesVKey tx = Set.fromList . fmap (makeWitnessVKey tx)

-- | From a list of key pairs and a set of key hashes required for a multi-sig
-- scripts, return the set of required keys.
makeWitnessesFromScriptKeys
  :: (Crypto crypto
     , Signable (DSIGN crypto) (TxBody crypto))
  => TxBody crypto
  -> Map (AnyKeyHash crypto) (KeyPair 'Regular crypto)
  -> Set (AnyKeyHash crypto)
  -> Set (WitVKey crypto)
makeWitnessesFromScriptKeys txb hashKeyMap scriptHashes =
  let witKeys    = Map.restrictKeys hashKeyMap scriptHashes
  in  makeWitnessesVKey txb (Map.elems witKeys)

-- |Determine the total balance contained in the UTxO.
balance :: Crypto crypto => UTxO crypto -> Value crypto
balance (UTxO utxo) = foldr (+) zeroV (Set.map getValue (range utxo))

-- |Determine the total deposit amount needed
totalDeposits
  :: PParams
  -> StakePools crypto
  -> [DCert crypto]
  -> Coin
totalDeposits pc (StakePools stpools) cs = foldl f (Coin 0) cs'
  where
    f coin cert = coin + dvalue cert pc
    notRegisteredPool (DCertPool (RegPool pool)) =
      Map.notMember (_poolPubKey pool) stpools
    notRegisteredPool _ = True
    cs' = filter notRegisteredPool cs

txup :: Tx crypto -> Update crypto
txup (Tx txbody _ _ _) = _txUpdate txbody

-- | Extract script hash from value address with script.
getScriptHash :: Addr crypto -> Maybe (ScriptHash crypto)
getScriptHash (AddrBase (ScriptHashObj hs) _)     = Just hs
getScriptHash (AddrPtr (ScriptHashObj hs) _)      = Just hs
getScriptHash (AddrEnterprise (ScriptHashObj hs)) = Just hs
getScriptHash _                                   = Nothing

scriptStakeCred
  :: DCert crypto
  -> Maybe (ScriptHash crypto)
scriptStakeCred (DCertDeleg (DeRegKey (KeyHashObj _)))    =  Nothing
scriptStakeCred (DCertDeleg (DeRegKey (ScriptHashObj hs))) = Just hs
scriptStakeCred (DCertDeleg (Delegate (Delegation (KeyHashObj _) _)))    =  Nothing
scriptStakeCred (DCertDeleg (Delegate (Delegation (ScriptHashObj hs) _))) = Just hs
scriptStakeCred _ = Nothing

scriptCred
  :: Credential crypto
  -> Maybe (ScriptHash crypto)
scriptCred (KeyHashObj _)  = Nothing
scriptCred (ScriptHashObj hs) = Just hs


-- | Computes the set of script hashes required to unlock the transcation inputs
-- and the withdrawals.
-- now runs the forging scripts too
scriptsNeeded
  :: Crypto crypto
  => UTxO crypto
  -> Tx crypto
  -> Set (ScriptHash crypto)
scriptsNeeded u tx =
  Set.fromList (Map.elems $ Map.mapMaybe (getScriptHash . getAddress) u'')
  `Set.union`
  Set.fromList (Maybe.mapMaybe (scriptCred . getRwdCred) $ Map.keys withdrawals)
  `Set.union`
  Set.fromList (Maybe.mapMaybe scriptStakeCred (filter requiresVKeyWitness certificates))
  `Set.union`
  Set.fromList (keys $ val $ _forge $ _body tx)
  where withdrawals = unWdrl $ _wdrls $ _body tx
        UTxO u'' = txinsScript (txins $ _body tx) u <| u
        certificates = (toList . _certs . _body) tx

-- | Compute the subset of inputs of the set 'txInps' for which each input is
-- locked by a script in the UTxO 'u'.
txinsScript
  :: Crypto crypto
  => Set (UTxOIn crypto)
  -> UTxO crypto
  -> Set (UTxOIn crypto)
txinsScript txInps (UTxO u) =
  txInps `Set.intersection`
  Map.keysSet (Map.filter (\utxoout ->
                               case getAddress utxoout of
                                 AddrBase (ScriptHashObj _) _     -> True
                                 AddrEnterprise (ScriptHashObj _) -> True
                                 AddrPtr (ScriptHashObj _) _      -> True
                                 _                                -> False) u)
