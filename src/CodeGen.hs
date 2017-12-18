{-# LANGUAGE TemplateHaskell #-}

module CodeGen where

import System.IO
import Data.String.Utils
import Debug.Trace
import Data.Map
import Control.Monad
import Control.Monad.Except
import Control.Lens

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
  modeName :: String,
  xde :: ODE, -- position dynamics
  bde :: ODE -- battery dynamics
} deriving (Show, Eq)

data Sensor = Sensor {
  sId :: Int,
  position :: Double,
  modes :: SensorMode
} deriving (Show, Eq)

type SensorMode = Map String ODE -- only has queue dynamics

data Mode = Mode {
  modeId :: Int,
  uavMode :: String,
  sensorMode :: String
} deriving (Show, Eq)

-- Overall specification (for parsing)
data Decls = Decls {
  _defns :: Defs,
  _varDomains :: Map String Domain,
  _modeDefs :: [Mode],
  _uavModes :: [UAVMode],
  _sensors :: [Sensor]
} deriving (Show, Eq)

makeLenses ''Decls

data CompleteSpec = CompleteSpec {
  _declarations :: Decls,
  _numModes :: Int,
  _allVars :: [String],
  _programParams :: [(String, Double)]
} deriving (Show, Eq)

makeLenses ''CompleteSpec

-- TODO: check well-formedness of specification?
-- TODO: reconstruct spec: adjust indices, anything else?
-- What else do we need to generate smt?
-- and to update the .smt2 each time?

-- Functions for converting specification to SMT-readable form

generateVars :: Decls -> [String]
generateVars ds = xs ++ bs ++ sqs ++ ts ++ ps
  where
    numModes = length (_modeDefs ds)
    numSensors = length (_sensors ds)
    ts = fmap (("t" ++) . show) [0..(numModes - 1)]
    xs = fmap (("x" ++) . show) [0..(numModes - 1)]
    bs = "bi" : fmap (("b" ++) . show) [0..(numModes - 1)]
    sls = fmap (\s -> "s" ++ show s ++ "_loc") [0..(numSensors - 1)]
    qs = "q_i" : fmap (("q" ++) . show) [0..(numModes - 1)]
    s = fmap (("s" ++) . show) [0..(numSensors - 1)]
    sqs = concatMap (\v -> fmap ((v ++ "_") ++) qs) s
    ps = "p0" : "p1" : fmap ("p2_" ++) s ++ fmap ("p3_" ++) s

generateSMT :: CompleteSpec -> String
generateSMT spec = unlines vdecls
  where
    vdecls = fmap declFun (_allVars spec)
    --decls = fmap declFun


-- Top-level
logic :: String
logic = "(set-logic QF_NRA)"

-- introducing vars / functions for smt
declFun :: String -> String
declFun s = "(declare-fun " ++ s ++ " () Real)"

initConstant :: String -> Double -> String
initConstant c x = "(assert (= " ++ c ++ " " ++ show x ++ "))"

-- only supports inclusive bounds for now
-- "sep" is a newline only if the variable has both upper and lower bounds
declBound :: String -> Maybe Double -> Maybe Double -> String
declBound v l h = m1 ++ sep ++ m2
  where
    m1 = case l of
      Nothing -> ""
      Just x  -> "(assert (>= " ++ v ++ " " ++ show x ++ "))"
    m2 = case h of
      Nothing -> ""
      Just y  -> "(assert (<= " ++ v ++ " " ++ show y ++ "))"
    sep = case (l, h) of
      (Just _, Just _) -> "\n"
      _                -> ""
