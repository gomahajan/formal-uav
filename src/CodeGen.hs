{-# LANGUAGE OverloadedStrings, TemplateHaskell #-}

module CodeGen where

import System.IO
import Data.String.Utils
import Debug.Trace
import Data.Map
import Control.Monad
import Control.Monad.Except
import Control.Lens
import Data.Text (splitOn)
import Data.List
import Data.String
import Data.Maybe

import Logic
import Pretty

--  Constant definitions
type Defs = Map String Double

-- For UAV and queue dynamics
type ODE = Exp

-- Position of sensor or UAV
type Position = Double

data Domain = Domain {
  vmin :: Maybe Double,
  vmax :: Maybe Double
} deriving (Show, Eq)

data UAVMode = UAVMode {
  modeName :: String,
  xde :: ODE, -- position dynamics
  bde :: ODE, -- battery dynamics
  prog :: [Pred]
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
  _environment :: Env,
  _numHoles :: Int,
  _invt :: Pred,
  _paramValues :: [(String, Double)]
} deriving (Show, Eq)

makeLenses ''Decls

data Vars = Vars {
  _allDomains :: [(String, Domain)],
  _allVars :: [String],
  _tvars :: [String],
  _xvars :: [String],
  _bvars :: [String],
  _qvars :: [String],
  _pvars :: [String],
  _expanded_qvars :: [String],
  _locvars :: [String],
  _cxVars :: [String],
  _initVars :: [String]
} deriving (Show, Eq)

makeLenses ''Vars


data CompleteSpec = CompleteSpec {
  _declarations :: Decls,
  _numModes :: Int,
  _numSensors :: Int,
  _vars :: Vars
} deriving (Show, Eq)

makeLenses ''CompleteSpec

{- DSL to CEGIS
  declarations:
    decl for all uavs: battery, position
    decl for all sensors: queue, location
    decl for all times
    decl choice

  initializations:
    wellformed battery <= 100, time >=0, queue >= 0, choice
    init for all queues:location

  dynamics:
    print_charge
    printFlyTo
    mode_emptying:
      forallsensors if choice = i, qdynamics2 si_q2 si_q1 forallothersensors qdynamics sk_q2 sk_q1
      bdynamics b2 b1
    printFlyFrom

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


-- Expand specification from declarations
finishSpec :: Decls -> CompleteSpec
finishSpec d = CompleteSpec {
  _declarations = d,
  _numModes = length (_uavModes d),
  _vars = generateVars d,
  _numSensors = length (_sensors d)
}


-- Functions for converting specification to SMT-readable form

-- Generate variable names for all modes alongside domains for relevant variables.
generateVars :: Decls -> Vars
generateVars ds = Vars {
  _allDomains = bdoms ++ qdoms,
  _allVars = xs ++ bs ++ sqs ++ ts ++ ks ++ sls ++ ps,
  _tvars = ts,
  _xvars = xs,
  _bvars = bs,
  _qvars = qs,
  _pvars = ps,
  _expanded_qvars = sqs,
  _locvars = sls,
  _cxVars = cxs,
  _initVars = inits
}
  where
    numModes = length (_modeDefs ds)
    numSensors = length (_sensors ds)
    ks = keys (_defns ds)
    ts = fmap (("t" ++) . show) [0..(numModes - 1)]
    xs = "xi" : fmap (("x" ++) . show) [0..(numModes - 1)]
    bs = "bi" : fmap (("b" ++) . show) [0..(numModes - 1)]
    sls = fmap (\s -> "s" ++ show s ++ "_loc") [0..(numSensors - 1)]
    qs = "qi" : fmap (("q" ++) . show) [0..(numModes - 1)]
    s = fmap (("s" ++) . show) [0..(numSensors - 1)]
    sqs = concatMap (\v -> fmap ((v ++ "_") ++) qs) s
    xdoms = zip xs (replicate numModes (_varDomains ds ! "x" ))
    bdoms = zip bs (replicate (numModes + 1) (_varDomains ds ! "b" ))
    qdoms = zip sqs (replicate (numSensors * (numModes + 1)) (_varDomains ds ! "q" ))
    ps = fmap fst (_paramValues ds)
    cxs = "bc" : fmap ((++ "_qc") . ("s" ++) . show) [0..(numSensors - 1)]
    inits = "bi" : fmap ((++ "_qi") . ("s" ++) . show) [0..(numSensors - 1)]

-- Get corresponding sensor mode from a UAV mode
uavModeToSensor :: String -> CompleteSpec -> Maybe String
uavModeToSensor s spec = fmap sensorMode mode
  where
    ms = (_modeDefs . _declarations) spec
    mode = find (\m -> uavMode m == s) ms

-- Inverse of above
sensorModeToUAV :: String -> CompleteSpec -> Maybe String
sensorModeToUAV s spec = fmap uavMode mode
  where
    ms = (_modeDefs . _declarations) spec
    mode = find (\m -> sensorMode m == s) ms

initializeParams :: CompleteSpec -> [String]
initializeParams spec = vdecls ++ cxdecs ++ tmin ++ doms ++ choice
  where
    env = _environment . _declarations $ spec
    numSensors = _numSensors spec
    cxs = mkvars "c"
    ivs = mkvars "i"
    cxdecs = fmap declFun cxs
    mkvars v = ("b" ++ v) : fmap ((++ ("_q" ++ v)) . ("s" ++) . show) [0..(numSensors - 1)]
    choice = initChoice env (_numSensors spec)
    allvars = _vars spec
    vdecls = fmap declFun $ tail (_xvars allvars) ++ _bvars allvars ++ _expanded_qvars allvars ++ _tvars allvars
    defList = assocs $ (_defns . _declarations) spec
    defs = zipWith initConstant (fmap fst defList) (fmap (show . snd) defList)
    tmin = fmap (`decMin` 0) ((_tvars . _vars) spec)
    doms = (fmap declBound ((_allDomains . _vars) spec)) ++ ["(assert (<= s0_qi 100.0))\n(assert (<= s1_qi 100.0))"]
    sensors = (_sensors . _declarations) spec


initializeParamConsts :: CompleteSpec -> [String]
initializeParamConsts spec = logic : (vdecls ++ initNorm ++ defs ++ slocs ++ pbounds)
  where
    params = (_pvars . _vars) spec
    locs = _locvars . _vars $ spec
    vdecls = fmap declFun $ params ++ keys ((_defns . _declarations) spec) ++ locs
    defList = assocs $ (_defns . _declarations) spec
    defs = zipWith initConstant (fmap fst defList) (fmap (show . snd) defList)
    -- TODO: generalize pmax below
    pdoms = replicate (length params) Domain {vmin = Just 0.0, vmax = Just 100.0}
    pdoms' = zip params pdoms
    pbounds = fmap declBound pdoms'
    sensors = (_sensors . _declarations) spec
    slocs = zipWith initConstant (fmap (\x -> "s" ++ (show (sId x) ++ "_loc")) sensors) (fmap (show . position) sensors)

-- Top-level declarations for SMT (mostly all function/variable declarations)
-- TODO: when the program is added it will need to be included here
initializeSMT :: CompleteSpec -> [String]
initializeSMT spec = logic : (vdecls ++ defs ++ slocs ++ tmin ++ doms ++ hole ++ choice)
  where
    env = _environment . _declarations $ spec
    hole = ["\nparametervalues\n"]
    choice = initChoice env (_numSensors spec)
    vdecls = fmap declFun ((_allVars . _vars) spec)
    defList = assocs $ (_defns . _declarations) spec
    defs = zipWith initConstant (fmap fst defList) (fmap (show . snd) defList)
    tmin = fmap (`decMin` 0) ((_tvars . _vars) spec)
    doms = fmap declBound ((_allDomains . _vars) spec)
    sensors = (_sensors . _declarations) spec
    slocs = zipWith initConstant (fmap (\x -> "s" ++ (show (sId x) ++ "_loc")) sensors) (fmap (show . position) sensors)

-- Prints all x,b,q dynamics for a given mode
printDynamics :: String -> CompleteSpec -> String -> String -> [String]
printDynamics mode spec curr prev = xds ++ bds ++ sens
  where
    bds = printDEs mode spec "b" curr prev bde
    xds = printDEs mode spec "x" curr prev xde
    qc = "q" ++ curr
    qp = "q" ++ prev
    smode = uavModeToSensor mode spec
    sens = printSensors spec smode qc qp ((_sensors . _declarations) spec)

-- TODO: refactor so that the following two functions are encapsulated in one
-- Prints dynamics for an arbitrary variable (b or q)
printDEs :: String -> CompleteSpec -> String -> String -> String -> (UAVMode -> ODE) -> [String]
printDEs mode spec var curr prev dynamics = [printConstraint env new]
  where
    env = _environment . _declarations $ spec
    vc = var ++ curr
    vp = var ++ prev
    uavm = find (\m -> modeName m == mode) ((_uavModes . _declarations) spec)
    vcon = case uavm of
      Nothing -> error "Invalid mode"
      Just m -> dynamics m
    new = Expr $ EBin Eq (EStrLit vc) (EBin Plus (EStrLit vp) vcon)


-- Labelling smt sections for readability/debugging
preamble :: String -> [String]
preamble title = "\n" : [";" ++ title]

printProgMode :: String -> CompleteSpec -> [String]
printProgMode name spec = fmap (printConstraint ((_environment . _declarations) spec)) (prog m')
  where
    modes = (_uavModes . _declarations) spec
    m = find (\x -> modeName x == name) modes
    m' = fromMaybe (error "Invalid mode") m

-- TODO: is it still ok to have x dynamics?
printCharge :: String -> CompleteSpec -> [String]
printCharge name spec = preamble "charging" ++ fmap (replace " t" " t0") (pos : dyn ++ prog)
  where
    pos = initConstant "x0" "0"
    dyn = tail $ printDynamics name spec (show 0) "i" --take tail to eliminate x dynamics
    prog = printProgMode name spec

-- Print mode flying from sensor to charge
printFlyFrom :: String -> CompleteSpec -> [String]
printFlyFrom name spec = preamble "flying back" ++ fmap (replace " t" " t3") (pos : dyn ++ prog)
  where
    pos = initConstant "x3" "0"
    dyn = printDynamics name spec (show 3) (show 2)
    prog = printProgMode name spec

-- Prints constraints for the "collect data" mode
-- This is impossible to understand sorry
-- But it works
-- ...
-- For now
printCollect :: String -> CompleteSpec -> [String]
printCollect name spec = preamble "Collecting data" ++ fmap (replace " t" " t2") (pos : battery ++ fmap (printConstraint env) completePred ++ prog)
  where
    env = _environment . _declarations $ spec
    -- battery dynamics
    uavm = sensorModeToUAV name spec
    battery = printDEs (fromMaybe name uavm) spec "b" "2" "1" bde
    -- Current position constraint
    pos = initConstant "x2" "x1"
    -- sensor stuff - this is a shitshow
    nums = _numSensors spec
    choices = fmap (Expr . EBin Eq (EStrLit "choice") . ERealLit . fromIntegral) [0..(nums - 1)]
    qs = fmap ((++ "_q2") . ("s" ++) . show) [0..(nums - 1)]
    prevqs = fmap ((++ "_q1") . ("s" ++) . show) [0..(nums - 1)]
    otherQs = assembleSensors qs
    otherPrevQs = assembleSensors prevqs
    sds = fmap modes ((_sensors . _declarations) spec)
    uploadDyn = Expr <$> zipWith3 (\q prevq ds -> EBin Eq (EStrLit q) (EBin Minus (EStrLit prevq) (ds ! "upload"))) qs prevqs sds
    allSensors = case unchosenSensors "collect" otherQs otherPrevQs ((_sensors . _declarations) spec) of
      Nothing -> fmap (: []) uploadDyn
      Just ps -> zipWith (:) uploadDyn ps
    completePred = zipWith (\c s -> Impl c (And s)) choices allSensors
    prog = printProgMode name spec

-- get dynamics for a given mode from a sensor with a given id number
getDE :: String -> Int -> [Sensor] -> ODE
getDE mode s sensors = case find (\x -> sId x == s) sensors of
  Nothing -> error "Can't find sensor"
  Just sen -> modes sen ! mode

-- "choice" variable choses a sensor -- this returns the dynamics of all sensors
--    not chosen
unchosenSensors :: String -> [[String]] -> [[String]] -> [Sensor] -> Maybe [[Pred]]
unchosenSensors _ [[]] _ _ = Nothing
unchosenSensors mode otherQs otherPrevQs sensors = Just $ zipWith (assemblePred mode sensors) otherPrevQs otherQs

-- Assemble differential equation dynamics into usable form via integration essentially
assemblePred :: String -> [Sensor] -> [String] -> [String] -> [Pred]
assemblePred mode s qs pqs = zipWith (\q pq -> Expr (EBin Eq (EStrLit pq) (EBin Plus (EStrLit q) (getDE mode (extractId pq) s)))) qs pqs

-- Get ID number out of a string describing a sensor
extractId :: String -> Int
extractId ('s':s) = Prelude.read $ fst (splitAt 1 s)
extractId _       = error "Malformed sensor id"

--convert a list of sensors into a corresponding list of lists of the OTHER sensors and their dynamics
assembleSensors :: [String] -> [[String]]
assembleSensors qs = fmap others qs
  where others q = Data.List.filter (/= q) qs

-- Print constraints for uav flying to sensor
printFlyTo :: String -> CompleteSpec -> [String]
printFlyTo name spec = preamble "flying to sensors" ++ fmap (replace " t" " t1") (fmap (printConstraint env) impls ++ dyn ++ prog)
  where
    env = _environment . _declarations $ spec
    numm = _numModes spec
    nums = _numSensors spec
    mkSensor x = "s" ++ show x ++ "_loc"
    impls = fmap ((\x -> Impl (Expr (EBin Eq (EStrLit "choice") (ERealLit (fromIntegral x)))) (Expr (EBin Eq (EStrLit "x1") (EStrLit (mkSensor x)))))) [0..(nums - 1)]
    dyn = printDynamics name spec (show 1) (show 0)
    prog = printProgMode name spec

-- Prints sensor dynamics for a given mode
printSensors :: CompleteSpec -> Maybe String -> String -> String -> [Sensor] -> [String]
printSensors _ Nothing _ _ _ = error "Invalid UAV mode"
printSensors spec (Just mode) modeNum prevModeNum sensors = fmap ((printConstraint env) . Expr) s
  where env = _environment . _declarations $ spec
        ids = fmap ((++ ("_" ++ modeNum)) . ("s" ++) . show . sId) sensors
        prevIds = fmap ((++ ("_" ++ prevModeNum)) . ("s" ++) . show . sId) sensors
        dyn = fmap ((! mode) . modes) sensors
        s = zipWith3 (\p c d -> (EBin Eq (EStrLit c) (EBin Plus (EStrLit p) d))) prevIds ids dyn

-- set s0qi = s0qc, etc, for parameter template
initEnd :: CompleteSpec -> [String]
initEnd spec = [printConstraint [] (And es)]
  where
    base = "b" : fmap ((++ "_q") . ("s" ++) . show) [0..(_numSensors spec - 1)]
    ps = fmap (++ "i") base
    cs = fmap (++ "c") base
    es = zipWith (\p c -> Expr (EBin Eq (EStrLit p) (EStrLit c))) ps cs


initNotGoal :: CompleteSpec -> [String]
initNotGoal spec = preamble "Goal" ++ ["(assert (not (=>" ++ initInvariant spec "i" ++ "(and "++ initSafety spec ++ initInvariant spec "3" ++ "))))"]
  where numSensors = _numSensors spec

initGoal :: CompleteSpec -> [String]
initGoal spec = preamble "Goal" ++ ["(assert (=>" ++ initInvariant spec "i" ++ "(and "++ initSafety spec ++ initInvariant spec "3" ++ ")))"]
  where numSensors = _numSensors spec

initSafety :: CompleteSpec -> String
initSafety spec = printConstraint' env (And (bbounds ++ sbounds))
  where
    numSensors = _numSensors spec
    env = _environment . _declarations $ spec
    qs = fmap (("_q" ++) . show) [0..3]
    s = fmap (("s" ++) . show) [0..(numSensors - 1)]
    sqs = concatMap (\sen -> fmap (sen ++) qs) s
    smax = vmax $ (_varDomains . _declarations) spec ! "q"
    smax' = fromMaybe 100.0 smax
    sbounds = fmap (\s -> Expr (EBin Lt (EStrLit s) (ERealLit smax'))) sqs
    bs = fmap (("b" ++) . show) [0..3]
    bmin = vmin $ (_varDomains . _declarations) spec ! "b"
    bmin' = fromMaybe 0.0 bmin
    bbounds = fmap (\b -> Expr (EBin Gt (EStrLit b) (ERealLit bmin'))) bs


-- This is wrong right now
initInvariant :: CompleteSpec -> String -> String
initInvariant spec index = printConstraint' env invt''
  where env =_environment . _declarations $ spec
        invt = _invt . _declarations $ spec
        invt' = replacePred "b" ("b" ++ index) invt
        invt'' = replacePred "q" ("q" ++ index) invt'

-- Initialize choice variable
initChoice :: Env -> Int -> [String]
initChoice env n = top : [ors]
  where
    top = declFun "choice"
    con = Or (fmap ((Expr . EBin Eq (EStrLit "choice") . ERealLit) . fromIntegral) [0..(n-1)])
    ors = printConstraint env con

initNorm :: [String]
initNorm = ["(define-fun norm ((a Real)) Real\n  (ite (< a 0) (* -1 a) a))"]

-- SMT syntax printing utilities

-- Top-level
logic :: String
logic = "(set-logic QF_NRA)"

endSMT :: [String]
endSMT = ["(check-sat)\n(exit)"]

-- introducing vars / functions for smt
declFun :: String -> String
declFun s = "(declare-fun " ++ s ++ " () Real)"

initConstant :: String -> String -> String
initConstant c x = "(assert (= " ++ c ++ " " ++ x ++ "))"

decMin :: String -> Double -> String
decMin s v = "(assert (>= " ++ s ++ " " ++ show v ++ "))"

declBound :: (String, Domain) -> String
declBound (v, d) = case (vmin d, vmax d) of
  (Nothing, Nothing) -> ""
  (Just low, Nothing) -> "(assert (>= " ++ v ++ " " ++ show low ++ "))"
  (Nothing, Just high) -> "(assert (<= " ++ v ++ " " ++ show high ++ "))"
  (Just low, Just high) -> "(assert (>= " ++ v ++ " " ++ show low ++ "))" ++ "\n" ++ "(assert (<= " ++ v ++ " " ++ show high ++ "))"

z3Footer :: CompleteSpec -> [String]
z3Footer spec = [sat, ps', ex]
  where
    sat = "(check-sat)"
    ps = unwords $ (_pvars . _vars) spec
    ps' = "(get-value (" ++ ps ++ "))"
    ex = "(exit)"
