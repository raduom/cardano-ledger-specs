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

module Shelley.Spec.Ledger.STS.Sval
  ( SVAL
  , SVALEnv (..)
  , SVALState (..)
  , PredicateFailure(..)
  )
where


import           Cardano.Binary (FromCBOR (..), ToCBOR (..), decodeListLen, decodeWord,
                     encodeListLen, matchSize)
import           Cardano.Prelude (NoUnexpectedThunks (..))
import           Control.State.Transition
import           Data.Typeable (Typeable)
import           Data.Word (Word8)
import           GHC.Generics (Generic)
import           Shelley.Spec.Ledger.BaseTypes
import           Shelley.Spec.Ledger.Crypto
import           Shelley.Spec.Ledger.PParams

import           Shelley.Spec.Ledger.Tx
import           Shelley.Spec.Ledger.UTxO

import           Shelley.Spec.Ledger.CostModel
import           Shelley.Spec.Ledger.Scripts

data SVAL crypto

data SVALState = SVALState ExUnits

data SVALEnv crypto
  = SVALEnv
      PParams
      (Tx crypto)
      deriving(Show)

instance
  Crypto crypto
  => STS (SVAL crypto)
 where
  type State (SVAL crypto) = SVALState
  type Signal (SVAL crypto) = [(ScriptPLC, [Data])]
  type Environment (SVAL crypto) = SVALEnv crypto
  type BaseM (SVAL crypto) = ShelleyBase
  data PredicateFailure (SVAL crypto)
    = BadTag
    deriving (Eq, Show, Generic)
  transitionRules = [svalInductive]
  initialRules = [initialValState]

instance NoUnexpectedThunks (PredicateFailure (SVAL crypto))

instance
  (Typeable crypto, Crypto crypto)
  => ToCBOR (PredicateFailure (SVAL crypto))
 where
   toCBOR = \case
     BadTag               -> encodeListLen 1 <> toCBOR (0 :: Word8)

instance
  (Crypto crypto)
  => FromCBOR (PredicateFailure (SVAL crypto))
 where
  fromCBOR = do
    n <- decodeListLen
    decodeWord >>= \case
      0 -> matchSize "BadTag" 1 n >> pure BadTag
      k -> invalidKey k

initialValState :: InitialRule (SVAL crypto)
initialValState = do
  IRC _ <- judgmentContext
  pure $ SVALState defaultUnits

svalInductive
  :: forall crypto
   . Crypto crypto
  => TransitionRule (SVAL crypto)
svalInductive = do
  TRC (SVALEnv pp tx, svs, sLst) <- judgmentContext
  let SVALState remExU = svs

  case (null sLst) of
    -- Scripts-Val rule for when all scripts have been run and validated
    True -> do
      (_valtag tx == IsValidating Nope) ?! BadTag
      (remExU < defaultUnits) ?! BadTag
      pure svs

    -- when there are scripts left to validate
    False -> do
      -- run the script and get validation result and remaining exunits
      let (sd, datas) = head sLst
      let ls = tail sLst
      let (isVal, remExU') = runPLCScript (getmdl (PlutusScriptV1 sd) pp) sd datas remExU

      -- validation tag is Nope - there should be a validation failure /
      -- run out of ExUnits / scripts left to validate
      -- Scripts-Stop rule in formal spec
      case (_valtag tx) of
        IsValidating Nope -> do
          (isVal == IsValidating Yes) ?! BadTag
          (remExU' > defaultUnits) ?! BadTag
          pure svs

      -- validation tag is Yes - script should validate, exunits budget remains
      -- Scripts-Ind rule in formal spec
        IsValidating Yes -> do
          (isVal == IsValidating Nope) ?! BadTag
          (remExU' <= defaultUnits) ?! BadTag
          trans @(SVAL crypto) $ TRC (SVALEnv pp tx, SVALState remExU', ls)
