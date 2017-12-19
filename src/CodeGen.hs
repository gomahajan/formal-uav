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
import Data.Typeable

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
  _sensors :: [Sensor]
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

makeLenses ''CompleteSpec

finishSpec :: Decls -> CompleteSpec
finishSpec d = CompleteSpec {
  _declarations = d,
  _numModes = length (_uavModes d),
  _vars = generateVars d,
  _numSensors = length (_sensors d)
}


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

-- Type encapsulating program and parameter values
data UAVParams = UAVParams {
  varNames :: [String]
} deriving (Show, Eq)

uavModeToSensor :: String -> CompleteSpec -> Maybe String
uavModeToSensor s spec = fmap sensorMode mode
  where
    ms = (_modeDefs . _declarations) spec
    mode = find (\m -> uavMode m == s) ms

initializeSMT :: UAVParams -> CompleteSpec -> [String]
initializeSMT params spec = logic : (vdecls ++ defs ++ slocs ++ tmin ++ doms ++ choice)
  where
    choice = initChoice (_numSensors spec)
    vdecls = fmap declFun ((_allVars . _vars) spec)
    defList = assocs $ (_defns . _declarations) spec
    defs = zipWith initConstant (fmap fst defList) (fmap (show . snd) defList)
    --plist = _programParams spec
    --initps = zipWith initConstant (fmap fst plist) (fmap snd plist)
    tmin = fmap (`decMin` 0) ((_tvars . _vars) spec)
    doms = fmap declBound ((_allDomains . _vars) spec)
    sensors = (_sensors . _declarations) spec
    slocs = zipWith initConstant (fmap (\x -> "s" ++ (show (sId x) ++ "_loc")) sensors) (fmap (show . position) sensors)

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
    smode = uavModeToSensor name spec
    sens = printSensors smode qc qp ((_sensors . _declarations) spec)

-- Labelling smt sections for debugging
preamble :: String -> [String]
preamble title = "\n" : [(";" ++ title)]

-- TODO: is it still ok to have x dynamics?
printCharge :: String -> UAVParams -> CompleteSpec -> [String]
printCharge name params spec = preamble "charging" ++ fmap (replace " t" " t3") (pos : dyn)
  where
    pos = initConstant "x0" "0"
    dyn = printDynamics name spec (show 1) "i"

printFlyFrom :: String -> UAVParams -> CompleteSpec -> [String]
printFlyFrom name params spec = preamble "flying back" ++ fmap (replace " t" " t3") (pos : dyn)
  where
    pos = initConstant "x3" "0"
    dyn = printDynamics name spec (show 3) (show 2)

printCollect :: String -> UAVParams -> CompleteSpec -> [String]
printCollect name params spec = preamble "Collecting data" ++ (fmap (replace " t" " t2") (pos : ([printConstraint newb] ++ fmap printConstraint completePred)))
  where
    -- battery dynamics
    uavm = find (\m -> modeName m == "download") ((_uavModes . _declarations) spec)
    bcon = case uavm of
      Nothing -> error "Invalid mode"
      Just m -> bde m
    newb = Expr $ EBin Eq (EStrLit "b2") (EBin Minus (EStrLit "b1") bcon)
    pos = initConstant "x2" "x1"
    -- sensors
    nums = _numSensors spec
    choices = fmap (Expr . EBin Eq (EStrLit "choice") . ERealLit . fromIntegral) [0..(nums - 1)]
    qs = fmap ((++ "_q2") . ("s" ++) . show) [0..(nums - 1)]
    prevqs = fmap ((++ "_q1") . ("s" ++) . show) [0..(nums - 1)]
    otherQs = assembleSensors qs
    otherPrevQs = assembleSensors prevqs
    sds = fmap modes ((_sensors . _declarations) spec)
    uploadDyn = fmap Expr $ zipWith3 (\q prevq ds -> EBin Eq (EStrLit q) (EBin Minus (EStrLit prevq) (ds ! "upload"))) qs prevqs sds
    --unchosen = zipWith (\qs pqs -> fmap (\q pq -> Expr $ getDE (extractId q) ((_sensors . _declarations) spec))) otherQs otherPrevQs
    allSensors = case unchosenSensors otherQs otherPrevQs ((_sensors . _declarations) spec) of
      Nothing -> fmap (: []) uploadDyn
      Just ps -> zipWith (:) uploadDyn ps
    completePred = zipWith (\c s -> Impl c (And s)) choices allSensors
    --collectDyn =
    --setDyn =
    --qcollect s = EBin Eq (EStrLit (s ++ "_q2") ())

getDE :: Int -> [Sensor] -> ODE
getDE s sensors = case find (\x -> sId x == s) sensors of
  Nothing -> error "Can't find sensor"
  Just sen -> modes sen ! "collect"

unchosenSensors :: [[String]] -> [[String]] -> [Sensor] -> Maybe [[Pred]]
unchosenSensors [[]] _ _ = Nothing
unchosenSensors otherQs otherPrevQs sensors = trace (show sensors) $ Just $ zipWith (assemblePred sensors) otherQs otherPrevQs

assemblePred :: [Sensor] -> [String] -> [String] -> [Pred]
assemblePred s qs pqs = trace (show (qs ++ pqs)) $ zipWith (\q pq -> Expr (EBin Plus (EStrLit pq) (EBin Eq (EStrLit q) (getDE (extractId pq) s)))) qs pqs

extractId :: String -> Int
extractId ('s':s) = Prelude.read $ fst (splitAt 1 s)
extractId _       = error "Malformed sensor id"

--convert a list of sensors into a corresponding list of lists of the OTHER sensors and their dynamics
assembleSensors :: [String] -> [[String]]
assembleSensors qs = (fmap others qs)
  where others q = Data.List.filter (\x -> x /= q) qs

printFlyTo :: String -> UAVParams -> CompleteSpec -> [String]
printFlyTo name params spec = preamble "flying to sensors" ++ fmap (replace " t" " t0") (fmap printConstraint impls ++ dyn)
  where
    numm = _numModes spec
    nums = _numSensors spec
    mkSensor x = "s" ++ show x ++ "_loc"
    impls = fmap ((\x -> Impl (Expr (EBin Eq (EStrLit "choice") (ERealLit x))) (Expr (EBin Eq (EStrLit "x1") (EStrLit (mkSensor x))))) . fromIntegral) [0..(nums - 1)]
    dyn = printDynamics name spec (show 1) (show 0)

printSensors :: Maybe String -> String -> String -> [Sensor] -> [String]
printSensors Nothing _ _ _ = error $ "Invalid UAV mode"
printSensors (Just mode) modeNum prevModeNum sensors = fmap (printConstraint . Expr) s
  where ids = fmap ((++ ("_" ++ modeNum)) . ("s" ++) . show . sId) sensors
        prevIds = fmap ((++ ("_" ++ prevModeNum)) . ("s" ++) . show . sId) sensors
        --dyn = concat $ fmap (elems . modes) sensors
        dyn = fmap ((! mode) . modes) sensors
        s = zipWith3 (\p c d -> (EBin Eq (EStrLit c) (EBin Plus (EStrLit p) d))) prevIds ids dyn

--printChoiceMode :: CompleteSpec -> String

-- For constant modes (ie flying from hard-coded location to another)
--printStaticMode :: CompleteSpec -> String

--TODO: automate this!
initGoal :: [String]
initGoal = preamble "Goal" ++ ["(assert (and (>= bi p0) (<= qi p1)))\n(assert (or (<= b0 0) (<= b1 0) (<= b2 0) (<= b3 0) (>= q0 100) (>= q1 100) (>= q2 100) (>= q3 100) (not (and (>= b3 p0) (<= q3 p1)))))"]

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

initConstant :: String -> String -> String
initConstant c x = "(assert (= " ++ c ++ " " ++ x ++ "))"

decMin :: String -> Double -> String
decMin s v = "(assert (>= " ++ s ++ " " ++ show v ++ "))"

declBound :: (String, Domain) -> String
declBound (v, d) = m1 ++ "\n" ++ m2
  where
    m1 = "(assert (>= " ++ v ++ " " ++ show (vmin d) ++ "))"
    m2 = "(assert (<= " ++ v ++ " " ++ show (vmax d) ++ "))"
