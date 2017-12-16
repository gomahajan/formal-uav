module CodeGen where

import System.IO
import Data.String.Utils
import Debug.Trace
import Data.Map
import Control.Monad
import Control.Monad.Except

import Logic

--  Constant definitions
type Defs = Map String Double

-- For UAV and queue dynamics
type ODE = Exp

-- Position of sensor or UAV
type Position = Double

data Domain = Domain {
  vmin :: Double,
  vmax :: Double
} deriving (Show, Eq)

data UAVMode = UAVMode {
  uavName :: String,
  xde :: ODE, -- position dynamics
  bde :: ODE -- battery dynamics
} deriving (Show, Eq)

data SensorDynamics = SensorDynamics {
  sensorName :: String,
  qde :: ODE -- queue dynamics
} deriving (Show, Eq)

type Sensors = Map String SensorDynamics

data Mode = Mode {
  modeName :: String,
  uavMode :: String,
  sensorMode :: String
} deriving (Show, Eq)

-- Overall specification
data Spec = Spec {
  defns :: Defs,
  varDomains :: Map String Domain,
  modeDefs :: Map String Mode,
  uavModes :: [UAVMode],
  sensors :: Sensors,
  sensorModes :: [String]
} deriving (Show, Eq)
