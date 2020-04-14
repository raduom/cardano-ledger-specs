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

module Shelley.Spec.Ledger.STS.Utxo
  ( UTXO
  , PredicateFailure(..)
  )
where

import           Byron.Spec.Ledger.Core (dom, range, (⊆), (◁))
import           Cardano.Binary (FromCBOR (..), ToCBOR (..), decodeListLen, decodeWord,
                     encodeListLen, matchSize)
import           Cardano.Prelude (NoUnexpectedThunks (..))
import           Control.State.Transition
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import           Data.Typeable (Typeable)
import           Data.Word (Word8)
import           GHC.Generics (Generic)
import           Shelley.Spec.Ledger.BaseTypes
import           Shelley.Spec.Ledger.Coin
import           Shelley.Spec.Ledger.Crypto
import           Shelley.Spec.Ledger.LedgerState (UTxOState (..), consumed,
                     minfee, produced, txsize)
import           Shelley.Spec.Ledger.PParams
import           Shelley.Spec.Ledger.Slot
import           Shelley.Spec.Ledger.STS.Utxos
import           Shelley.Spec.Ledger.Tx
import           Shelley.Spec.Ledger.TxData (getValue, UTxOOut(..), UTxOOutP (..), txinputsvf, utxoref)
import           Shelley.Spec.Ledger.UTxO
import           Shelley.Spec.Ledger.Value

import           Shelley.Spec.Ledger.CostModel

data UTXO crypto

instance
  Crypto crypto
  => STS (UTXO crypto)
 where
  type State (UTXO crypto) = UTxOState crypto
  type Signal (UTXO crypto) = Tx crypto
  type Environment (UTXO crypto) = UtxoEnv crypto
  type BaseM (UTXO crypto) = ShelleyBase
  data PredicateFailure (UTXO crypto)
    = BadInputsUTxO
    | BeforeLiveIntervalUTxO SlotNo SlotNo
    | ExpiredUTxO SlotNo SlotNo
    | MaxTxSizeUTxO Integer Integer
    | TooManyExUnits ExUnits ExUnits
    | InputSetEmptyUTxO
    | FeeTooSmallUTxO Coin Coin
    | PlutusOutputsPayingFeesUTxO
    | NonAdaFeeUTxO
    | ForFeeInputsTooSmallUTxO Coin Coin
    | ValueNotConservedUTxO ValueBSType ValueBSType
    | NegativeOutputsUTxO
    | ForgingAda
    | UTXOSChecksFailure (PredicateFailure (UTXOS crypto))
    deriving (Eq, Show, Generic)
  transitionRules = [utxoInductive]
  initialRules = [initialLedgerStateUTXO]

instance NoUnexpectedThunks (PredicateFailure (UTXO crypto))

instance
  (Typeable crypto, Crypto crypto)
  => ToCBOR (PredicateFailure (UTXO crypto))
 where
   toCBOR = \case
     BadInputsUTxO               -> encodeListLen 1 <> toCBOR (0 :: Word8)
     (ExpiredUTxO a b)           -> encodeListLen 3 <> toCBOR (1 :: Word8)
                                      <> toCBOR a <> toCBOR b
     (MaxTxSizeUTxO a b)         -> encodeListLen 3 <> toCBOR (2 :: Word8)
                                      <> toCBOR a <> toCBOR b
     InputSetEmptyUTxO           -> encodeListLen 1 <> toCBOR (3 :: Word8)
     (FeeTooSmallUTxO a b)       -> encodeListLen 3 <> toCBOR (4 :: Word8)
                                      <> toCBOR a <> toCBOR b
     (ValueNotConservedUTxO a b) -> encodeListLen 3 <> toCBOR (5 :: Word8)
                                      <> toCBOR a <> toCBOR b
     NegativeOutputsUTxO         -> encodeListLen 1 <> toCBOR (6 :: Word8)
     ForgingAda                  -> encodeListLen 1 <> toCBOR (7 :: Word8)
     (UTXOSChecksFailure a)           -> encodeListLen 2 <> toCBOR (8 :: Word8)
                                      <> toCBOR a
     PlutusOutputsPayingFeesUTxO -> encodeListLen 1 <> toCBOR (9 :: Word8)
     NonAdaFeeUTxO               -> encodeListLen 1 <> toCBOR (10 :: Word8)
     (ForFeeInputsTooSmallUTxO a b) -> encodeListLen 3 <> toCBOR (11 :: Word8)
                                     <> toCBOR a <> toCBOR b
     (BeforeLiveIntervalUTxO a b)-> encodeListLen 3 <> toCBOR (12 :: Word8)
                                     <> toCBOR a <> toCBOR b
     (TooManyExUnits a b)        -> encodeListLen 3 <> toCBOR (13 :: Word8)
                                     <> toCBOR a <> toCBOR b

instance
  (Crypto crypto)
  => FromCBOR (PredicateFailure (UTXO crypto))
 where
  fromCBOR = do
    n <- decodeListLen
    decodeWord >>= \case
      0 -> matchSize "BadInputsUTxO" 1 n >> pure BadInputsUTxO
      1 -> do
        matchSize "ExpiredUTxO" 3 n
        a <- fromCBOR
        b <- fromCBOR
        pure $ ExpiredUTxO a b
      2 -> do
        matchSize "MaxTxSizeUTxO" 3 n
        a <- fromCBOR
        b <- fromCBOR
        pure $ MaxTxSizeUTxO a b
      3 -> matchSize "InputSetEmptyUTxO" 1 n >> pure InputSetEmptyUTxO
      4 -> do
        matchSize "FeeTooSmallUTxO" 3 n
        a <- fromCBOR
        b <- fromCBOR
        pure $ FeeTooSmallUTxO a b
      5 -> do
        matchSize "ValueNotConservedUTxO" 3 n
        a <- fromCBOR
        b <- fromCBOR
        pure $ ValueNotConservedUTxO a b
      6 -> matchSize "NegativeOutputsUTxO" 1 n >> pure NegativeOutputsUTxO
      7 -> matchSize "ForgingAda" 1 n >> pure ForgingAda
      8 -> do
        matchSize "UTXOSChecksFailure" 2 n
        a <- fromCBOR
        pure $ UTXOSChecksFailure a
      9 -> matchSize "PlutusOutputsPayingFeesUTxO" 1 n >> pure PlutusOutputsPayingFeesUTxO
      10 -> matchSize "NonAdaFeeUTxO" 1 n >> pure NonAdaFeeUTxO
      11 -> do
        matchSize "ForFeeInputsTooSmallUTxO" 3 n
        a <- fromCBOR
        b <- fromCBOR
        pure $ ForFeeInputsTooSmallUTxO a b
      12 -> do
        matchSize "BeforeLiveIntervalUTxO" 3 n
        a <- fromCBOR
        b <- fromCBOR
        pure $ BeforeLiveIntervalUTxO a b
      13 -> do
        matchSize "TooManyExUnits" 3 n
        a <- fromCBOR
        b <- fromCBOR
        pure $ TooManyExUnits a b
      k -> invalidKey k


initialLedgerStateUTXO
  :: forall crypto
   . ( Crypto crypto )
   => InitialRule (UTXO crypto)
initialLedgerStateUTXO = do
  IRC (UtxoEnv slots pp stakeCreds stakepools genDelegs) <- judgmentContext
  trans @(UTXOS crypto) $ IRC (UtxoEnv slots pp stakeCreds stakepools genDelegs)

utxoInductive
  :: forall crypto
   . Crypto crypto
  => TransitionRule (UTXO crypto)
utxoInductive = do
  TRC (UtxoEnv slot pp stakeCreds stakepools genDelegs, u, tx) <- judgmentContext
  let UTxOState utxo _ _ _ = u
  let txb = _body tx

  -- tx within liveness interval
  _fst txb <= slot ?! BeforeLiveIntervalUTxO (_fst txb) slot
  _ttl txb >= slot ?! ExpiredUTxO (_ttl txb) slot

  -- tx has at least one input
  txins txb /= Set.empty ?! InputSetEmptyUTxO

  -- fee checks
  let minFee = minfee pp tx
      txFee  = _txfee txb
  -- enough to cover min fee
  minFee <= txFee ?! FeeTooSmallUTxO minFee txFee

  let (UTxO feeouts) = (Set.map utxoref (txinputsvf $ _inputs $ _body $ tx)) ◁ utxo
  let forfees = getAdaAmount $ balance (UTxO feeouts)
  -- no for-fee inputs correspond to Plutus locked outputs
  not (null [ (inp, ot) | (inp , ot@(UTxOOutPT (UTxOOutP _ _ _) _)) <- Map.toList feeouts ]) ?! PlutusOutputsPayingFeesUTxO

  -- for-fee outputs contain only Ada
  (balance (UTxO feeouts) == (coinToValue $ getAdaAmount $ balance (UTxO feeouts))) ?! NonAdaFeeUTxO

  -- make sure the fee inputs are enough to cover "given"
  txFee <= forfees ?! ForFeeInputsTooSmallUTxO forfees txFee

  -- inputs all in UTxO
  txins txb ⊆ dom utxo ?! BadInputsUTxO

  -- general accounting property
  let consumed_ = consumed pp utxo stakeCreds txb
      produced_ = produced slot pp stakepools txb
  consumed_ == produced_ ?! ValueNotConservedUTxO (toValBST consumed_) (toValBST produced_)

  -- all tx outputs are non negative
  let outputValues = [getValue utxoout | utxoout <- Set.toList (range (txouts slot txb))]
  all (zeroV <=) outputValues ?! NegativeOutputsUTxO

  -- not forging ada
  let (Value vls) = _forge txb
  let cids = Map.keys vls
  all (adaID /=) cids  ?! ForgingAda

  -- tx too big
  let maxTxSize_ = fromIntegral (_maxTxSize pp)
      txSize_ = txsize tx
  txSize_ <= maxTxSize_ ?! MaxTxSizeUTxO txSize_ maxTxSize_

  -- tx exceeds ExUnits limit per Tx
  _exunits txb <= (_maxTxExUnits pp) ?! TooManyExUnits (_exunits txb) (_maxTxExUnits pp)

  -- the UTXOS rule
  trans @(UTXOS crypto)
    $ TRC (UtxoEnv slot pp stakeCreds stakepools genDelegs, u, tx)

-- wrap UTXOS failure
instance
  ( Crypto crypto)
  => Embed (UTXOS crypto) (UTXO crypto)
 where
  wrapFailed = UTXOSChecksFailure
