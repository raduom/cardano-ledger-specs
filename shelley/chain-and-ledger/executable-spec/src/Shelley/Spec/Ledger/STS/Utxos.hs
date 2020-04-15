{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Shelley.Spec.Ledger.STS.Utxos
  ( UTXOS
  , UtxoEnv (..)
  , PredicateFailure(..)
  )
where

import           Byron.Spec.Ledger.Core ((∪), (⋪), (◁))
import           Cardano.Binary (FromCBOR (..), ToCBOR (..), decodeListLen, decodeWord,
                     encodeListLen, matchSize)
import           Cardano.Prelude (NoUnexpectedThunks (..))
import           Control.State.Transition
import           Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import           Data.Typeable (Typeable)
import           Data.Word (Word8)
import           GHC.Generics (Generic)
import           Shelley.Spec.Ledger.BaseTypes
import           Shelley.Spec.Ledger.Coin
import           Shelley.Spec.Ledger.Crypto
import           Shelley.Spec.Ledger.Delegation.Certificates
import           Shelley.Spec.Ledger.Keys
import           Shelley.Spec.Ledger.LedgerState (UTxOState (..), decayedTx, keyRefunds)
import           Shelley.Spec.Ledger.PParams
import           Shelley.Spec.Ledger.Slot
import           Shelley.Spec.Ledger.STS.Ppup
import           Shelley.Spec.Ledger.STS.Sval
import           Shelley.Spec.Ledger.Tx
import           Shelley.Spec.Ledger.TxData (utxoref, txinputsvf)
import           Shelley.Spec.Ledger.UTxO
import           Shelley.Spec.Ledger.Value

import           Shelley.Spec.Ledger.Scripts
import           Shelley.Spec.Ledger.CostModel

data UTXOS crypto

data UtxoEnv crypto
  = UtxoEnv
      SlotNo
      PParams
      (StakeCreds crypto)
      (StakePools crypto)
      (GenDelegs crypto)
      deriving(Show)

instance
  Crypto crypto
  => STS (UTXOS crypto)
 where
  type State (UTXOS crypto) = UTxOState crypto
  type Signal (UTXOS crypto) = Tx crypto
  type Environment (UTXOS crypto) = UtxoEnv crypto
  type BaseM (UTXOS crypto) = ShelleyBase
  data PredicateFailure (UTXOS crypto)
    = ScriptValFailure (PredicateFailure (SVAL crypto))
    | UpdateFailure (PredicateFailure (PPUP crypto))
    deriving (Eq, Show, Generic)
  transitionRules = [scriptsYesNo]
  initialRules = [initialLedgerState]

instance NoUnexpectedThunks (PredicateFailure (UTXOS crypto))

instance
  (Typeable crypto, Crypto crypto)
  => ToCBOR (PredicateFailure (UTXOS crypto))
 where
   toCBOR = \case
     (ScriptValFailure a)           -> encodeListLen 2 <> toCBOR (0 :: Word8)
                                      <> toCBOR a
     (UpdateFailure a)           -> encodeListLen 2 <> toCBOR (1 :: Word8)
                                      <> toCBOR a

instance
  (Crypto crypto)
  => FromCBOR (PredicateFailure (UTXOS crypto))
 where
  fromCBOR = do
    n <- decodeListLen
    decodeWord >>= \case
      0 -> do
        matchSize "ScriptValFailure" 2 n
        a <- fromCBOR
        pure $ ScriptValFailure a
      1 -> do
        matchSize "UpdateFailure" 2 n
        a <- fromCBOR
        pure $ UpdateFailure a
      k -> invalidKey k

initialLedgerState :: InitialRule (UTXOS crypto)
initialLedgerState = do
  IRC _ <- judgmentContext
  pure $ UTxOState (UTxO Map.empty) (Coin 0) (Coin 0) emptyPPPUpdates


-- | represents all transition rules
scriptsYesNo
  :: forall crypto
   . Crypto crypto
  => TransitionRule (UTXOS crypto)
scriptsYesNo = do
  TRC (UtxoEnv slot pp stakeCreds stakepools genDelegs, u, tx) <- judgmentContext
  let UTxOState utxo deposits fees ppup = u
  let txb = _body tx

  -- make a list of scripts and their inputs for snd validation phase
  let sLst = mkPLCLst utxo tx

  -- run Plutus scripts
  -- TODO is this the right order of things for two-phase validation?
  let exu SNothing   = defaultUnits
      exu (SJust ex) = ex
  _ <- trans @(SVAL crypto) $ TRC (SVALEnv pp tx, SVALState (exu $ _exunits txb), sLst)

  case (_valtag tx) of
    -- Scripts-No rule for when one of the Plutus scripts does not validate
    IsValidating Nope -> do
      -- get fees inputs and outputs
      let feeins = Set.map utxoref (txinputsvf $ _inputs $ _body $ tx)
      let feeouts = feeins ◁ utxo
      let forfees = getAdaAmount $ balance feeouts

      pure UTxOState
            { _utxo      = feeins ⋪ utxo
            , _deposited = deposits
            , _fees      = fees + forfees
            , _ppups     = ppup
            }

    -- Scripts-Yes rule for when all Plutus scripts validate
    IsValidating Yes -> do
      -- process Protocol Parameter Update Proposals
      ppup' <- trans @(PPUP crypto) $ TRC (PPUPEnv slot pp genDelegs, ppup, txup tx)

      let refunded = keyRefunds pp stakeCreds txb
      decayed <- liftSTS $ decayedTx pp stakeCreds txb
      let txCerts = toList $ _certs txb
      let depositChange = totalDeposits pp stakepools txCerts - (refunded + decayed)

      pure UTxOState
            { _utxo      = (txins txb ⋪ utxo) ∪ txouts slot txb
            , _deposited = deposits + depositChange
            , _fees      = fees + (_txfee txb) + decayed
            , _ppups     = ppup'
            }

instance Crypto crypto
  => Embed (PPUP crypto) (UTXOS crypto)
 where
  wrapFailed = UpdateFailure


instance Crypto crypto
  => Embed (SVAL crypto) (UTXOS crypto)
 where
  wrapFailed = ScriptValFailure
