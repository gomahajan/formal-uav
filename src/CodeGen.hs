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
import Pretty

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
  _sensors :: [Sensor],
  _initialParams :: [(String, Double)]
} deriving (Show, Eq)

makeLenses ''Decls

data Vars = Vars {
  _allDomains :: [(String, Domain)],
  _allVars :: [String],
  _tvars :: [String],
  _xvars :: [String],
  _bvars :: [String],
  _qvars :: [String]
} deriving (Show, Eq)

makeLenses ''Vars

data CompleteSpec = CompleteSpec {
  _declarations :: Decls,
  _numModes :: Int,
  _programParams :: [(String, Double)],
  _numSensors :: Int,
  _vars :: Vars
} deriving (Show, Eq)

makeLenses ''CompleteSpec

finishSpec :: Decls -> CompleteSpec
finishSpec d = CompleteSpec {
  _declarations = d,
  _numModes = length (_uavModes d),
  _vars = generateVars d,
  _programParams = expandParams (_initialParams d),
  _numSensors = nums
} where
  nums = length (_sensors d)
  expandParams [] = []
  expandParams (p:ps) = case fst p of
    "p0" -> p : expandParams ps
    "p1" -> p : expandParams ps
    "p2" -> allParams p nums ++ expandParams ps
    "p3" -> allParams p nums ++ expandParams ps
    _    -> error "Invalid parameter declaration"

-- Expand each parameter
allParams :: (String, Double) -> Int -> [(String, Double)]
allParams p numS = zip (fmap ((((fst p) ++ "_s") ++) . show) [0..(numS - 1)]) (replicate numS (snd p))

-- TODO: check well-formedness of specification?
-- TODO: reconstruct spec: adjust indices, anything else?
-- What else do we need to generate smt?
-- and to update the .smt2 each time?

-- Functions for converting specification to SMT-readable form

generateVars :: Decls -> Vars
generateVars ds = Vars {
  _allDomains = xdoms ++ bdoms ++ qdoms,
  _allVars = xs ++ bs ++ sqs ++ ts ++ ps,
  _tvars = ts,
  _xvars = xs,
  _bvars = bs,
  _qvars = qs
}
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
    xdoms = zip xs (replicate numModes (_varDomains ds ! "x" ))
    bdoms = zip bs (replicate (numModes + 1) (_varDomains ds ! "b" ))
    qdoms = zip sqs (replicate (numSensors * (numModes + 1)) (_varDomains ds ! "q" ))

initializeSMT :: CompleteSpec -> [String]
initializeSMT spec = logic : (vdecls ++ defs ++ initps ++ slocs ++ tmin ++ doms ++ choice)
  where
    choice = initChoice (_numSensors spec)
    vdecls = fmap declFun ((_allVars . _vars) spec)
    defList = assocs $ (_defns . _declarations) spec
    defs = zipWith initConstant (fmap fst defList) (fmap snd defList)
    plist = _programParams spec
    initps = zipWith initConstant (fmap fst plist) (fmap snd plist)
    tmin = fmap (\t -> decMin t 0) ((_tvars . _vars) spec)
    doms = fmap declBound ((_allDomains . _vars) spec)
    sensors = (_sensors . _declarations) spec
    slocs = zipWith initConstant (fmap (\x -> "s" ++ (show (sId x) ++ "_loc")) sensors) (fmap position sensors)

initChoice :: Int -> [String]
initChoice n = top : [ors]
  where
    top = declFun "choice"
    con = Or (fmap (\y -> (Expr (EBin Eq (EStrLit "choice") (ERealLit y)))) (fmap fromIntegral [0..(n-1)]))
    ors = printConstraint con

-- Top-level
logic :: String
logic = "(set-logic QF_NRA)"

-- introducing vars / functions for smt
declFun :: String -> String
declFun s = "(declare-fun " ++ s ++ " () Real)"

initConstant :: String -> Double -> String
initConstant c x = "(assert (= " ++ c ++ " " ++ show x ++ "))"

decMin :: String -> Double -> String
decMin s v = "(assert (>= " ++ s ++ " " ++ show v ++ "))"

declBound :: (String, Domain) -> String
declBound (v, d) = m1 ++ "\n" ++ m2
  where
    m1 = "(assert (>= " ++ v ++ " " ++ show (vmin d) ++ "))"
    m2 = "(assert (<= " ++ v ++ " " ++ show (vmax d) ++ "))"
