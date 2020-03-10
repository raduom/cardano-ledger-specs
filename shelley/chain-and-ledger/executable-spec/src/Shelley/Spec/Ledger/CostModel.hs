{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Shelley.Spec.Ledger.CostModel
  where


import           Cardano.Prelude (NoUnexpectedThunks(..))
import           GHC.Generics (Generic)
import           Data.Word (Word8)
import           Cardano.Binary (FromCBOR (fromCBOR), ToCBOR (toCBOR),
                     encodeListLen, enforceSize)
import           Data.Map.Strict (Map, empty)
import           Shelley.Spec.Ledger.Coin
import           Shelley.Spec.Ledger.Serialization (CBORMap (..))

-- | comparing required resources for Plutus scripts
instance Ord ExUnits where
   (<=) (ExUnits rs1 mu1) (ExUnits rs2 mu2) =
     ((<=) rs1 rs2) && ((<=) mu1 mu2)

-- | cost models per language
data CostModels = CostModels (Map Language CostMod)
  deriving (Show, Eq, Generic)

-- | empty cost model map
defaultModels :: CostModels
defaultModels = CostModels empty

instance NoUnexpectedThunks CostModels

instance ToCBOR CostModels where
  toCBOR = toCBOR . CBORMap . getCMs
    where
      getCMs (CostModels cms) = cms

instance FromCBOR CostModels where
  fromCBOR = CostModels . unwrapCBORMap <$> fromCBOR

-- | language tags
newtype Language = Language Word8
  deriving (Show, Eq, Generic, NoUnexpectedThunks, Ord, ToCBOR, FromCBOR)

-- | Temporary stand-in for actual types in the execution cost
-- for Plutus script execution
data ExUnits = ExUnits
  { -- | The types of computational resources relevant to the cost model
      reductionSteps           :: Integer
    , memoryUnits              :: Integer
  } deriving (Show, Eq, Generic)

instance NoUnexpectedThunks ExUnits

-- | Temporary stand-in for actual types in the cost model
-- for Plutus script execution
-- TODO use this from Plutus
data CostMod = CostMod
  { -- | The types of computational resources relevant to the cost model
      smt                   :: ExUnits
    , smtElse               :: ExUnits
  } deriving (Show, Eq, Generic)

instance NoUnexpectedThunks CostMod

-- | Default values
-- | Default execution units
defaultUnits :: ExUnits
defaultUnits = ExUnits 0 0

-- | Default cost model
defaultModel :: CostMod
defaultModel = CostMod (ExUnits 0 0) (ExUnits 0 0)


-- | Prices for Plutus script execution
data Prices = Prices
  { -- | The types of computational resources relevant to the cost model
    initPrim               :: Coin
  , memPrim                :: Coin
  , stepPrim               :: Coin
  } deriving (Show, Eq, Generic)

instance NoUnexpectedThunks Prices


-- | Default cost model
defaultPrices :: Prices
defaultPrices = Prices (Coin 0) (Coin 0) (Coin 0)

-- | The formula for conversion of execution cost into Ada
scriptFee :: Integer -> Prices -> ExUnits -> Coin
scriptFee numScr (Prices (Coin i) (Coin m) (Coin s)) (ExUnits mu su) =
  Coin (numScr*i + m*mu + s*su)


-- | CBOR temp

instance FromCBOR ExUnits
 where
   fromCBOR = do
     enforceSize "ExUnits" 2
     a <- fromCBOR
     b <- fromCBOR
     pure $ ExUnits a b


instance ToCBOR ExUnits
 where
   toCBOR exu =
     encodeListLen 2
       <> toCBOR (reductionSteps exu)
       <> toCBOR (memoryUnits exu)

instance ToCBOR CostMod
 where
   toCBOR cm =
     encodeListLen 2
       <> toCBOR (smt cm)
       <> toCBOR (smtElse cm)

instance FromCBOR CostMod
 where
   fromCBOR = do
     enforceSize "CostMod" 2
     a <- fromCBOR
     b <- fromCBOR
     pure $ CostMod a b


instance
 ToCBOR Prices
 where
   toCBOR pr =
     encodeListLen 2
       <> toCBOR (initPrim pr)
       <> toCBOR (memPrim pr)
       <> toCBOR (stepPrim pr)


instance
 FromCBOR Prices
 where
   fromCBOR = do
     enforceSize "Prices" 3
     a <- fromCBOR
     b <- fromCBOR
     c <- fromCBOR
     pure $ Prices a b c
