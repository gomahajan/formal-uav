{-# LANGUAGE DeriveDataTypeable #-}

module Main where

import System.IO
import Data.String.Utils
import System.Environment
import System.Directory
import Debug.Trace
import System.Console.CmdArgs
import Data.Map (fromList, (!))
import Control.Monad
import Data.ConfigFile
import Data.Either.Utils
import Data.Maybe
import Control.Monad.Except
import Numeric

import Logic
import Parser
import SMTSolver
import Pretty
import CodeGen
import Utils

programName = "TBD"
versionName = "0.0"

{- Command Line Args -}


{-# ANN module "HLint: ignore Use camelCase" #-}

data CommandLineArgs = Args {
  smt_file :: String, -- file prefix
  depth :: Int,
  precision :: Double,
  smt_precision :: Double,
  verbose :: Bool,
  b_init :: Double,
  q_init :: Double,
  cx_balls :: Bool,
  log_file :: String
} deriving (Data, Typeable, Show, Eq)

cargs = Args {
  smt_file      = ""         &= argPos 0,
  depth         = 1000       &= help "Maximum number of iterations when running synthesis algorithm.",
  precision     = 0.1        &= help "Precision for hybrid system synthesis.",
  smt_precision = 0.001      &= help "Delta-precision for SMT solver.",
  verbose       = False      &= help "Verbose mode.",
  b_init        = 50         &= help "Initial battery level",
  q_init        = 50         &= help "Initial queue level",
  cx_balls      = False      &= help "Adjust counterexamples using delta-ball (probably unnecessary and potentially damaging!)",
  log_file      = "test/log" &= help "File for logging intermediate details."
}


data Params = Params {
  completeFile :: String,
  templateFile :: String,
  paramTempFile :: String,
  paramCompleteFile :: String,
  paramConstantFile :: String,
  originalIters :: Int,
  iterations :: Int,
  synthesisPrecision :: Double,
  solverPrecision :: Double,
  bcxs :: [Double],
  qcxs :: [Double],
  qcxs2 :: [Double],
  allcxs :: [[(String, Double)]],
  params :: [(String, Double)],
  verboseMode :: Bool,
  solverConfig :: SolverConfig,
  cxBalls :: Bool,
  shouldLog :: Bool,
  logFile :: String
} deriving (Show, Eq)


readConfig :: String -> IO SolverConfig
readConfig f = do
  rv <- runExceptT $ do
    cp <- Control.Monad.join $ liftIO $ readfile emptyCP f
    let x = cp
    dpath <- get x "DEFAULT" "path"
    dv    <- get x "DEFAULT" "version"
    dargs <- get x "DEFAULT" "args"
    zpath <- get x "DEFAULT" "z3_path"
    return SolverConfig {
      solverArgs = dargs,
      dRealVersion = dv,
      dRealPath = dpath,
      z3Path = zpath
    }
  either (error . snd) return rv


{- Algorithm: We ask dReal the following question: Starting from region specified by constraints,
is it possible to end in a state not specified by the constraints?
If dReal says no, then we have found a region which is safe/stable wrt battery and queue size.

Otherwise, it gives us counterexample bi,qi. We ask another question to dReal, starting from bi,qi
and other examples, find parameters for invariant and program which work. And this continues.
-}

cegisLoop :: Params -> CompleteSpec -> IO (Maybe ([(String, Double)], Bool))
cegisLoop p spec =
  if iterations p <= 0
  then return $ Just (params p, False)
  else do
    let paramStr = unlines (fmap ((printConstraint []) . Expr) (zipWith (EBin Eq) (fmap (EStrLit . fst) (params p)) (fmap (ERealLit . snd) (params p))))
        balls = findAllCXBalls (synthesisPrecision p) (allcxs p)
        ballStr = case (cxBalls p, balls) of
          (False, _) -> ""
          (True, [])    -> ""
          (True, bs) -> printConstraint [] (And (fmap Not bs))
    --putStrLn paramStr
    addParams (paramStr ++ "\n" ++ ballStr) (templateFile p) (completeFile p)
    when (verboseMode p) $ putStrLn "Finding counterexample..."
    output <- run (dRealVersion (solverConfig p)) (solverConfig p) (completeFile p) (solverPrecision p)
    resp <- Main.read (dRealVersion (solverConfig p)) output
    --putStrLn $ show resp
    let cxs = getCX ((_initVars . _vars) spec) resp
    --print cxs
    case cxs of
      Nothing -> do
        putStrLn $ "\n\nIn " ++ show (originalIters p - iterations p) ++ " iterations:"
        return $ Just (params p, True)
      Just cxs -> do
        let --(c1,c2) = findCXBall (previous_b p) (previous_q p) c1_naive c2_naive (synthesisPrecision p)
            allcxs' = cxs : allcxs p
            --bcxs' = c1 : bcxs p
            --qcxs' = c2 : qcxs p
            --qcxs2' = c3 : qcxs2 p
        --putStrLn $ "bcxs: " ++ show bcxs'
        --putStrLn $ "qcxs: " ++ show qcxs'
        when (verboseMode p) $ putStrLn $ "Adding Counterexample: " ++ show cxs
        addAllPhis p spec allcxs'
        when (verboseMode p) $ putStrLn "Finding parameters..."
        new_params_output <- run 2 (solverConfig p) (paramCompleteFile p) (solverPrecision p)
        new_params_output_string <- Main.read 2 new_params_output
        --putStrLn $ "Previous params: " ++ show (params p)
        if unsatResp new_params_output_string
        then return $ Just (params p, False)
        else do
          let ps' = fmap ((flip getValue) new_params_output_string) (fmap fst (params p))
              params' = zip (fmap fst (params p)) ps'
              currentIter = iterations p
          when (shouldLog p) $ appendFile (logFile p) (genCSV (fmap snd (cxs ++ params')))
          putStrLn $ "Solved Params: " ++ show params'
        --putStrLn $ "Previous params: " ++ show (params p)
          cegisLoop p { iterations = currentIter - 1,
                        allcxs = allcxs',
                        params = params'
                        } spec

-- As an alternative to CEGIS for generating the invariant, we propose simply expressing the entire problem as an existential logic formula
existentialSynthesis :: Params -> CompleteSpec -> IO (Maybe ([(String, Double)], Bool))
existentialSynthesis p spec =
  return Nothing

unsatResp :: Response -> Bool
unsatResp (Response _ []) = True
unsatResp _               = False

createParameterBall :: [(String, Double)] -> Double -> String
createParameterBall a eps = "(assert (> "++ (createParameterSum a)++ " "++ "1" ++ "))"

createParameterSum :: [(String, Double)] -> String
createParameterSum [(a,b)] = "(norm (- "++ a ++" "++ show b ++ "))"
createParameterSum (x:xs) = "(+ " ++ (createParameterSum [x]) ++ " " ++ (createParameterSum xs) ++ ")"

addAllPhis :: Params -> CompleteSpec -> [[(String, Double)]] -> IO ()
addAllPhis p spec cxs = do
  str <- addAllPhis' spec (paramTempFile p) (length cxs) cxs
  let parameterBalls = createParameterBall (params p) (synthesisPrecision p)
  let phis = unlines (parameterBalls : str) --fmap
  s <- readFile (paramConstantFile p)
  --putStrLn $ "PHIS:\n" ++ phis
  let s_i = replace "counterexamples" phis s
  writeFile (paramCompleteFile p) s_i

defaultPhis :: IO [String]
defaultPhis = return [""]

addAllPhis' :: CompleteSpec -> String -> Int -> [[(String, Double)]] -> IO [String]
addAllPhis' spec file k [x] = do s <- createPhi spec file x (show k)
                                 return [s]
addAllPhis' spec file n (x:xs) = do s <- createPhi spec file x (show n)
                                    s' <- addAllPhis' spec file (n - 1) xs
                                    return $ s : s'

createPhi :: CompleteSpec -> String -> [(String, Double)] -> String -> IO String
createPhi spec file cxs name = do
  s <- readFile file
  -- TODO: automate this
  let cvars = _cxVars vars
      andTerm = "(assert (and " ++ unwords eqs ++ "))"
      mkeq c (_,v) = "(= " ++ c ++ " " ++ (Numeric.showFFloat Nothing v "") ++ ")"
      eqs = zipWith mkeq cvars cxs
      s_i = replace "batteryvalue" andTerm s
      -- TODO: automate this
      vars = _vars spec
      variables = tail (_xvars vars) ++ _bvars vars ++ _expanded_qvars vars ++ _tvars vars ++ cvars ++ ["choice"]
      --variables = ["x0", "x1", "x2", "x3", "bi", "b0", "b1", "b2", "b3", "s1_qi", "s1_q0", "s1_q1", "s1_q2", "s1_q3", "s2_qi", "s2_q0", "s2_q1", "s2_q2", "s2_q3", "t0", "t1", "t2", "t3", "bc", "s1_qc", "s2_qc", "choice"]
      s_i_g = foldl (\str v -> (replace v (v ++ "_" ++ name) str)) s_i variables
  return s_i_g

{- Adds the counterexample and its implied space to the constraints -}
updateConstraint :: (Double, Double) -> Pred -> Pred
updateConstraint (b,q) _ = And [Expr $ EBin Eq (EVar "b") (ERealLit b), Expr $ EBin Eq (EVar "q") (ERealLit q)]

makeEqPred :: String -> Double -> Pred
makeEqPred s v = Expr $ EBin Eq (EVar s) (ERealLit v)

generateVarConstraints :: String -> String -> [Double] -> [Double] -> Pred
generateVarConstraints = generateVarConstraints' []

generateVarConstraints' :: [Pred] -> String -> String -> [Double] -> [Double] -> Pred
generateVarConstraints' ps s1 s2 [] _ = Or ps
generateVarConstraints' ps s1 s2 _ [] = Or ps
generateVarConstraints' ps s1 s2 (x:xs) (y:ys) = generateVarConstraints' (p':ps) s1 s2 xs ys
  where p' = generateAndTerm s1 s2 x y

generateAndTerm :: String -> String -> Double -> Double -> Pred
generateAndTerm s1 s2 v1 v2 = And [makeEqPred s1 v1, makeEqPred s2 v2]

generateAndTerm3 :: String -> String -> String -> Double -> Double -> Double -> Pred
generateAndTerm3 s1 s2 s3 v1 v2 v3= And [makeEqPred s1 v1, makeEqPred s2 v2, makeEqPred s3 v3]

-- Read solver response
read :: Int -> String -> IO Response
read n src = return $ parseDRealSat n src


-- Extract Counterexample from solver response
getCX :: [String] -> Response -> Maybe [(String, Double)]
getCX s (Response _ []) = Nothing
getCX s (Response r vs) = vals
  where
    ms = fmap (`lookup` vs) s
    exists m = case m of
      Nothing -> False
      Just _  -> True
    bothJust m1 m2 = m1 && exists m2
    allFound = foldl bothJust True ms
    vals = if allFound
           then Just $ zip s (fmap (fromMaybe 0.0) ms)
           else Nothing

getValue :: String -> Response -> Double
getValue s (Response r vs) = (fromList vs) ! s

--findCXBalls :: [Double] -> [Double] -> Double -> Double -> Double -> (Double, Double)
--findCXBalls [] [] x y _ = (x,y)
--findCXBalls []

findAllCXBalls :: Double -> [[(String, Double)]] -> [Pred]
findAllCXBalls epsilon = fmap (findCXBall epsilon)

findCXBall :: Double -> [(String, Double)] -> Pred
--findCXBall x y epsilon = (bi - x)^2 + (qi - y)^2 <= epsilon^2
findCXBall epsilon cxs = Expr $ EBin Geq (EBin Pow (ERealLit epsilon) (ERealLit 2)) plus
  where
    mknorm (s,v) = (EBin Pow (EBin Minus (EVar s) (ERealLit v)) (ERealLit 2))
    norms = fmap mknorm cxs
    plus = foldl (\p1 p2 -> EBin Plus p1 p2) (ERealLit 0) norms


getTheta :: Double -> Double -> Double
getTheta y x = if x == 0
               then pi / 2
               else atan (y/x)

--phi :: Double -> Double -> String


-- Create SMT with new constraints. Also overwrites if it already exists --
addConstraints :: String -> String -> String -> String -> IO ()
addConstraints tmpf cmpf constraintI constraintG = do
  s <- readFile tmpf
  let s_i = replace "constraintI" constraintI s
  let s_i_g  = replace "constraintG" constraintG s_i
  writeFile cmpf s_i_g

addParams :: String -> String -> String -> IO ()
addParams ps infile outfile  = do
  s <- readFile infile
  let pstr = replace "parametervalues" ps s
  writeFile outfile pstr

addInitialConstraint :: String -> String -> String -> IO ()
addInitialConstraint ps infile outfile = do
  s <- readFile infile
  let pstr = replace "batteryvalues" ps s
  writeFile outfile pstr

mode = cmdArgsMode $ cargs &=
  help "Hybrid system synthesizer" &=
  program programName &=
  summary (programName ++ " v" ++ versionName)

-- utility function
printParam :: (String, Double) -> String
printParam (p,x) = p ++ " = " ++ show x

-- Create uav_dreal_template.smt2
writeTemplate :: Params -> CompleteSpec -> IO ()
writeTemplate p spec = do
  let f = templateFile p
      smt = initializeSMT spec
      charge = printCharge "charge" spec
      flyto = printFlyTo "fly_to" spec
      collect = printCollect "download" spec
      flyfrom = printFlyFrom "fly_back" spec
  writeFile f (unlines (smt ++ charge ++ flyto ++ collect ++ flyfrom ++ initNotGoal spec ++ endSMT))

-- Create uav_dreal_paramterer_template.smt2
writeParamTemplate :: Params -> CompleteSpec -> IO ()
writeParamTemplate p spec = do
  let f = paramTempFile p
      top = initializeParams spec
      charge = printCharge "charge" spec
      flyto = printFlyTo "fly_to" spec
      collect = printCollect "download" spec
      flyfrom = printFlyFrom "fly_back" spec
      hole = ["\nbatteryvalue\n"]
      safety = initEnd spec ++ initGoal spec
  writeFile f $ unlines (top ++ charge ++ flyto ++ collect ++ flyfrom ++ hole ++ safety)

-- Create uav_dreal_parameter_constant_template.smt2
-- TODO: doesn't do the norm function for now -- is that necessary? we don't use it...
writeParamConstTemplate :: Params -> CompleteSpec -> IO ()
writeParamConstTemplate p spec = do
  let f = paramConstantFile p
      top = initializeParamConsts spec
      hole = ["\ncounterexamples\n"]
      footer = z3Footer spec
  writeFile f (unlines (top ++ hole ++ footer))


-- Entry point
main :: IO ()
main = do
  conf <- readConfig "config/solver.cfg"
  args <- cmdArgsRun mode
  case args of
    (Args file iters precision delta v b q balls lf) -> do
      let tmpf = file ++ "_template.smt2"
          cmpf = file ++ "_complete.smt2"
          paramtf = file ++ "_parameter_template.smt2"
          paramcf = file ++ "_parameter_complete.smt2"
          paramcons = file ++ "_parameter_constant_template.smt2"
          synthesisParams = Params {
            completeFile = cmpf,
            templateFile = tmpf,
            paramTempFile = paramtf,
            paramCompleteFile = paramcf,
            paramConstantFile = paramcons,
            originalIters = iters,
            iterations = iters,
            synthesisPrecision = precision,
            solverPrecision = delta,
            bcxs = [],
            qcxs = [],
            qcxs2 = [],
            allcxs = [],
            params = [], -- updated in prepareTemplates
            verboseMode = v,
            solverConfig = conf,
            cxBalls = balls,
            shouldLog = True, -- Change to false to turn off logging
            logFile = lf
          }
      when v $ putStrLn $ "Intial point: " ++ "(" ++ show b ++"," ++ show q ++ ")"
      --parse declarations etc
      x <- parseFromFile parseDecls file
      case x of
        Left e -> error $ show e
        Right decls -> do
          -- TODO: update params synthesisParams with the initial values parsed from spec!!
          let spec = finishSpec decls
              ps = synthesisParams { params = (_paramValues . _declarations) spec }
              --ps = synthesisParams { params = [("p0", 9), ("p1", 0), ("p2", 10), ("p3", 1), ("p4", 9), ("p5", 9), ("p6", 10), ("p7", 1), ("p8", 9), ("p9", 9)] }
          writeTemplate ps spec
          writeParamTemplate ps spec
          writeParamConstTemplate ps spec
          -- Prep log file
          when (shouldLog ps) $ writeFile (logFile ps) (genCSV (((_initVars . _vars) spec) ++ ((_pvars . _vars) spec)))
          p <- cegisLoop ps spec
          case p of
            Nothing -> putStrLn "Synthesis error"
            Just pr -> do
              putStrLn $ case pr of
                (_, False) -> "\nThe given system is unverifiable in " ++ show iters ++ " iterations"
                (ps, True)  -> "\nSynthesized a program with the following parameters: \n" ++ unlines (fmap printParam ps) ++
                  "\nAnd the following invariant:\n" ++ "b >= " ++ show (snd (head ps)) ++ "\nq <= " ++ show (snd (head (tail ps)))
              --removeFile (templateFile synthesisParams)
              --removeFile (paramTempFile synthesisParams)
              --removeFile (paramConstantFile synthesisParams)
              --removeFile (paramCompleteFile synthesisParams)
              --comment out the above to keep the smt2 files for reference.
