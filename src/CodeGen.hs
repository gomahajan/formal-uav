{-# LANGUAGE TemplateHaskell #-}

module CodeGen where

import System.IO
import Data.String.Utils
import Debug.Trace
import Data.Map
import Control.Monad
import Control.Monad.Except
import Control.Lens
import Data.List

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

{- DSL to CEGIS
  declarations:
    decl for all uavs: battery, position
    decl for all sensors: queue, location
    decl for all times
    decl choice

  initializations:
    wellformed battery <= 100, time >=0, queue >= 0, choice
    init for all queues:location

  counterexampleStep
    decl all parameters
    declarations

    init all parameters
    initializations

    dynamics

    not (invariant (bi, all sensor qi) => (safe and invariant (b3, all sensor q3)))

  parameterStep
    decl all parameters
    init all parameters

    for each counter-example
      declarations
      initializations
      init battery, all sensor queues to counterexample
      dynamics
      invariant (bi, all sensor qi) => (safe and invariant (b3, all sensor q3))
-}

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
    tmin = fmap (`decMin` 0) ((_tvars . _vars) spec)
    doms = fmap declBound ((_allDomains . _vars) spec)
    sensors = (_sensors . _declarations) spec
    slocs = zipWith initConstant (fmap (\x -> "s" ++ (show (sId x) ++ "_loc")) sensors) (fmap position sensors)

printDynamics :: String -> CompleteSpec -> String -> String -> [String]
printDynamics name spec curr prev = [printConstraint newx] ++ [printConstraint newb] ++ sens
  where
    xc = "x" ++ curr
    bc = "b" ++ curr
    qc = "q" ++ curr
    xp = "x" ++ prev
    bp = "b" ++ prev
    qp = "q" ++ prev
    uavm = find (\m -> modeName m == name) ((_uavModes . _declarations) spec)
    xcon = case uavm of
      Nothing -> error "Invalid mode"
      Just m -> xde m
    newx = Expr $ EBin Eq (EStrLit xc) (EBin Plus (EStrLit xp) xcon)
    bcon = case uavm of
      Nothing -> error "Invalid mode"
      Just m -> bde m
    newb = Expr $ EBin Eq (EStrLit bc) (EBin Plus (EStrLit bp) bcon)
    sens = printSensors name qc qp ((_sensors . _declarations) spec)

-- TODO: is it still ok to have x dynamics?
printCharge :: String -> CompleteSpec -> [String]
printCharge name spec = fmap (replace " t" " t3") (pos : dyn)
  where
    pos = initConstant "x0" 0.0
    dyn = printDynamics name spec (show 1) "i"

printFlyFrom :: String -> CompleteSpec -> [String]
printFlyFrom name spec = fmap (replace " t" " t3") (pos : dyn)
  where
    pos = initConstant "x3" 0.0
    dyn = printDynamics name spec (show 3) (show 2)

-- decision when to stop charging/collecting
--printDecision :: CompleteSpec -> [String]
--printDecision spec

printFlyTo :: String -> CompleteSpec -> [String]
printFlyTo name spec = fmap (replace " t" " t0") (fmap printConstraint impls ++ dyn)
  where
    numm = _numModes spec
    nums = _numSensors spec
    mkSensor x = "s" ++ show x ++ "_loc"
    impls = fmap ((\x -> Impl (Expr (EBin Eq (EStrLit "choice") (ERealLit x))) (Expr (EBin Eq (EStrLit "x1") (EStrLit (mkSensor x))))) . fromIntegral) [0..(nums - 1)]
    dyn = printDynamics name spec (show 1) (show 0)

printSensors :: String -> String -> String -> [Sensor] -> [String]
printSensors mode modeNum prevModeNum sensors = fmap (printConstraint . Expr) s
  where ids = fmap ((++ ("_" ++ modeNum)) . ("s" ++) . show . sId) sensors
        prevIds = fmap ((++ ("_" ++ prevModeNum)) . ("s" ++) . show . sId) sensors
        dyn = concat $ fmap (elems . modes) sensors
        s = zipWith3 (\p c d -> (EBin Eq (EStrLit c) (EBin Plus (EStrLit p) d))) prevIds ids dyn
--printChoiceMode :: CompleteSpec -> String

-- For constant modes (ie flying from hard-coded location to another)
--printStaticMode :: CompleteSpec -> String

--TODO: automate this!
initGoal :: String
initGoal = "(assert (and (>= bi p0) (<= qi p1)))\n(assert (or (<= b0 0) (<= b1 0) (<= b2 0) (<= b3 0) (>= q0 100) (>= q1 100) (>= q2 100) (>= q3 100) (not (and (>= b3 p0) (<= q3 p1)))))"

initChoice :: Int -> [String]
initChoice n = top : [ors]
  where
    top = declFun "choice"
    con = Or (fmap ((\y -> (Expr (EBin Eq (EStrLit "choice") (ERealLit y)))) . fromIntegral) [0..(n-1)])
    ors = printConstraint con

-- Top-level
logic :: String
logic = "(set-logic QF_NRA)"

endSMT :: String
endSMT = "(check-sat)\n(exit)"

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
