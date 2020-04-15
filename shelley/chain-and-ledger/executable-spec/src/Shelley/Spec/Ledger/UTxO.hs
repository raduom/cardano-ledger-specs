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
  , mkPLCLst
  , getmdl
  ) where

import           Cardano.Binary (FromCBOR (..), ToCBOR (..))
import           Cardano.Crypto.Hash (hashWithSerialiser)
import           Cardano.Prelude (NoUnexpectedThunks (..))
import           Data.Foldable (toList)
import           Data.Map.Strict (Map, keys, empty, insert, findWithDefault)
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
import           Data.Set (Set)
import qualified Data.Set as Set

import           Byron.Spec.Ledger.Core (Relation (..))
import           Shelley.Spec.Ledger.BaseTypes (strictMaybeToMaybe)
import           Shelley.Spec.Ledger.Coin (Coin (..))
import           Shelley.Spec.Ledger.Crypto
import           Shelley.Spec.Ledger.Keys (AnyKeyHash, KeyDiscriminator (..), KeyPair, Signable,
                     hash, sKey, sign, vKey, verify)
import           Shelley.Spec.Ledger.PParams (PParams, Update, _costmdls)
import           Shelley.Spec.Ledger.Tx (Tx (..), _txwits)
import           Shelley.Spec.Ledger.TxData (Addr (..), Credential (..), pattern DeRegKey, PoolParams(..),
                     pattern Delegate, pattern Delegation, PoolCert (..), TxBody (..),
                     UTxOIn (..), UTxOOut (..), OutND (..), TxOutP (..), UTxOOutP (..), XOutND (..),
                     TxId (..), TxIn (..), TxOut (..), Wdrl (..), WitVKey (..),
                     RdmrPtr(..), Rdmrs(..), CurItem (..), ScrTypes(..), RewardAcnt(..),
                     getRwdCred, utxoref, getValue, getAddress, _scripts, _dats, _rdmrs)
import           Shelley.Spec.Ledger.Slot (SlotNo (..))

import           Data.Coerce (coerce)
import           Shelley.Spec.Ledger.Delegation.Certificates (DCert (..), StakePools (..), dvalue,
                     requiresVKeyWitness)
import           Shelley.Spec.Ledger.Scripts
import           Shelley.Spec.Ledger.Value
import           Shelley.Spec.Ledger.CostModel

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
txid = TxId . hashWithSerialiser toCBOR

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
  Map.fromList [(UTxOIn transId idx, mkUTxOout s out) | (out, idx) <- zip (toList $ _outputs tx) [0..]]
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

txup :: Crypto crypto => Tx crypto -> Maybe (Update crypto)
txup (Tx txbody _ _ _) = strictMaybeToMaybe (_txUpdate txbody)

-- | Extract script hash from value address with script.
getScriptHash :: Addr crypto -> Maybe (ScriptHash crypto)
getScriptHash (Addr (ScriptHashObj hs) _) = Just hs
getScriptHash _                           = Nothing

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

-- | make hash-indexed structure of scripts
indexedScripts
  :: Crypto crypto
  => Tx crypto
  -> Map (ScriptHash crypto) (Script crypto)
indexedScripts tx
  = foldl (\m s -> insert (hashAnyScript s) s m) empty (_scripts $ _txwits tx)

-- | make hash-indexed structure of datums
indexedDatums
  :: Crypto crypto
  => Tx crypto
  -> Map (DataHash crypto) Data
indexedDatums tx
  = foldl (\m d -> insert (hashData d) d m) empty (_dats $ _txwits tx)

-- | find cost model for the script type
getmdl
  :: Script crypto
  -> PParams
  -> CostMod
getmdl (PlutusScriptV1 _) pp
  = findWithDefault defaultModel (Language plcV1) cms
    where
      (CostModels cms) = (_costmdls pp)
getmdl (MultiSigScript _) _ = defaultModel

-- | get the redeemer corresponding to the given current item
-- it should return just one redeemer - the type is a set for totality
findRdmr
  :: Crypto crypto
  => Tx crypto
  -> CurItem crypto
  -> [Data]
findRdmr tx ci = [ dat |
  (p , dat) <- Map.toList rds , elem p (getPtr ci (_body tx)) ]
  where
    Rdmrs rds = _rdmrs $ _txwits tx


-- | make the redeemer pointer
getPtr
  :: CurItem crypto
  -> TxBody crypto
  -> [RdmrPtr]
getPtr (TI r) txb
  = [ RdmrPtr InputTag idx |
    (ins, idx) <- zip (toList $ _inputs txb) [0..], ins == r ]
getPtr (SH r) txb
  = [ RdmrPtr ForgeTag idx |
    ((vl, _), idx) <- zip (Map.toList $ v) [0..], vl == r ]
  where
    Value v = _forge txb
getPtr (DC r) txb
  = [ RdmrPtr CertTag idx |
    (cs, idx) <- zip (toList $ _certs txb) [0..], cs == r ]
getPtr (WD r) txb
  = [ RdmrPtr WdrlTag idx |
    ((wl, _), idx) <- zip (Map.toList $ w) [0..], wl == r ]
  where
    Wdrl w = _wdrls txb

-- | this map assembles all the data needed to validate Plutus script-locked certificates
allCertScrts :: (Crypto crypto)
  => UTxO crypto
  -> Tx crypto
  -> [(ScriptPLC, [Data])]
allCertScrts utxo tx =
  [ (s_plc, [r, valContext utxo tx (DC c)]) |
    (cr, PlutusScriptV1 s_plc) <- Map.toList $ indexedScripts tx,
    c@(DCertDeleg (DeRegKey (ScriptHashObj sh))) <- toList $ _certs $ _body tx,
    r <- findRdmr tx (DC c),
    cr == sh ]

-- | this map assembles all the data needed to validate Plutus script-locked withdrawals
allWDRLSScrts :: (Crypto crypto)
  => UTxO crypto
  -> Tx crypto
  -> [(ScriptPLC, [Data])]
allWDRLSScrts utxo tx =
  [ (s_plc, [r, valContext utxo tx (WD wd)]) |
    (wd@(RewardAcnt (ScriptHashObj ra)), _) <- Map.toList $ unWdrl $ _wdrls $ _body tx,
    (cr, PlutusScriptV1 s_plc) <- Map.toList $ indexedScripts tx,
    r <- findRdmr tx (WD wd),
    cr == ra ]

-- | this map assembles all the data needed to validate all forges
forgedScrts :: (Crypto crypto)
  => UTxO crypto
  -> Tx crypto
  -> [(ScriptPLC, [Data])]
forgedScrts utxo tx =
   [ (s_plc, [r, valContext utxo tx (SH cid)]) |
    (cid, _) <- Map.toList $ val $ _forge $ _body tx,
    (cr, PlutusScriptV1 s_plc) <- Map.toList $ indexedScripts tx,
    r <- findRdmr tx (SH cid),
    cr == cid ]


-- | this map assembles all the data needed to validate Plutus script-locked outputs
-- TODO does this work right with pointer addresses?
allInsScrts :: (Crypto crypto)
  => UTxO crypto
  -> Tx crypto
  -> [(ScriptPLC, [Data])]
allInsScrts utxo tx =
   [ (s_plc, [d, r, valContext utxo tx (TI txin)]) |
    -- input from transaction
    txin <- Set.toList $ _inputs $ _body tx,
    -- a script hash and corresponding PLC script
    (cr, PlutusScriptV1 s_plc) <- Map.toList $ indexedScripts tx,
    -- redeemer associated with the tx input
    r <- findRdmr tx (TI txin),
    -- utxo entry
    (utxoin, UTxOOutPT (UTxOOutP a _ udh) _) <- Map.toList mutx,
    -- datum hash and cooresponding datum
    (dh, d) <- Map.toList $ indexedDatums tx,
    -- transaction input matches the utxo input
    utxoref txin == utxoin,
    -- utxo entry address script hash matches script hash from indexed script map
    Just cr == getScriptHash a,
    -- utxo entry datum hash matches datum hash from the indexed datum map
    udh == dh ]
      where
        UTxO mutx  = utxo


-- | returns all the Plutus scripts that must be run,
-- matched with their corresponding inputs
mkPLCLst :: (Crypto crypto)
  => UTxO crypto
  -> Tx crypto
  -> [(ScriptPLC, [Data])]
mkPLCLst utxo tx = (allCertScrts utxo tx) ++ (allWDRLSScrts utxo tx)
  ++ (forgedScrts utxo tx) ++ (allInsScrts utxo tx)

-- | Computes the set of script hashes required to unlock the transcation inputs
-- and the withdrawals.
-- now runs the forging scripts too
scriptsNeeded
  :: Crypto crypto => UTxO crypto
  -> Tx crypto
  -> Set (ScriptHash crypto) -- TODO Map (CurItem crypto) (ScriptHash crypto)
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
  -- forge

-- | Compute the subset of inputs of the set 'txInps' for which each input is
-- locked by a script in the UTxO 'u'.
txinsScript
  :: Set (UTxOIn crypto)
  -> UTxO crypto
  -> Set (UTxOIn crypto)
txinsScript txInps (UTxO u) =
  txInps `Set.intersection`
  Map.keysSet (Map.filter (\utxoout ->
                               case getAddress utxoout of
                                 Addr (ScriptHashObj _) _     -> True
                                 _                                -> False) u)


-- | TODO : make validation data to pass to Plutus validator
valContext :: UTxO crypto -> Tx crypto -> CurItem crypto -> Data
valContext _ _ _ = Data 1
