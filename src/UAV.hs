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
import Control.Monad.Except
import Numeric

import Logic
import Parser
import SMTSolver
import Pretty
import CodeGen

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
  q_init :: Double
} deriving (Data, Typeable, Show, Eq)

cargs = Args {
  smt_file      = ""    &= argPos 0,
  depth         = 1000    &= help "Maximum number of iterations when running synthesis algorithm.",
  precision     = 0.01  &= help "Precision for hybrid system synthesis.",
  smt_precision = 0.001 &= help "Delta-precision for SMT solver.",
  verbose       = False &= help "Verbose mode.",
  b_init        = 50    &= help "Initial battery level",
  q_init        = 50    &= help "Initial queue level"
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
  params :: [(String, Double)],
  previous_b :: Maybe Double, -- could rename to previous counter-example
  previous_q :: Maybe Double,
  verboseMode :: Bool,
  solverConfig :: SolverConfig
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
        balls = findAllCXBalls (synthesisPrecision p) (zip3 (bcxs p) (qcxs p) (qcxs2 p))
        ballStr = case balls of
          [] -> ""
          bs -> printConstraint [] (And (fmap Not bs))
    --putStrLn paramStr
    addParams (paramStr ++ "\n" ++ ballStr) (templateFile p) (completeFile p)
    when (verboseMode p) $ putStrLn "Finding counterexample..."
    output <- run (dRealVersion (solverConfig p)) (solverConfig p) (completeFile p) (solverPrecision p)
    resp <- Main.read (dRealVersion (solverConfig p)) output
    putStrLn $ show resp
    let cxs = getCX "bi" "s0_qi" "s1_qi" resp
    --print cxs
    case cxs of
      Nothing -> do
        putStrLn $ "\n\nIn " ++ show (originalIters p - iterations p) ++ " iterations:"
        return $ Just (params p, True)
      Just (c1, c2, c3) -> do
        let --(c1,c2) = findCXBall (previous_b p) (previous_q p) c1_naive c2_naive (synthesisPrecision p)
            bcxs' = c1 : bcxs p
            qcxs' = c2 : qcxs p
            qcxs2' = c3 : qcxs2 p
            --constraintbq = "(assert (=> (and (and (>= bi p0) (<= qi p1)) constraintbq) (and (> b0 0) (> b1 0) (> b2 0) (> b3 0) (< q0 100) (< q1 100) (< q2 100) (< q3 100) (and (>= b3 p0) (<= q3 p1)))))"
            -- replace "constraintbq" with
            -- battery_constraint = printConstraint $ generateVarConstraints "bi" "qi" bcxs' qcxs'
            --battery_constraint = unlines $ fmap (((flip (replace "constraintbq")) constraintbq) . printConstraint') (zipWith (findCXBall (synthesisPrecision p)) bcxs' qcxs')
        --putStrLn $ "bcxs: " ++ show bcxs'
        --putStrLn $ "qcxs: " ++ show qcxs'
        when (verboseMode p) $ putStrLn $ "Adding Counterexample: " ++ show (c1, c2, c3)
        addAllPhis p spec $ zip3 bcxs' qcxs' qcxs2'
        when (verboseMode p) $ putStrLn "Finding parameters..."
        new_params_output <- run 2 (solverConfig p) (paramCompleteFile p) (solverPrecision p)
        new_params_output_string <- Main.read 2 new_params_output
        --putStrLn $ "Previous params: " ++ show (params p)
        if unsatResp new_params_output_string
        then return $ Just (params p, False)
        else do
          let ps' = fmap ((flip getValue) new_params_output_string) (fmap fst (params p))
              params' = zip (fmap fst (params p)) ps'
              {-
              p0 = getValue "p0" new_params_output_string
              p1 = getValue "p1" new_params_output_string
              p2 = getValue "p2" new_params_output_string
              p3 = getValue "p3" new_params_output_string
              p4 = getValue "p4" new_params_output_string
              p5 = getValue "p5" new_params_output_string
              p6 = getValue "p6" new_params_output_string
              p7 = getValue "p7" new_params_output_string
              p8 = getValue "p8" new_params_output_string
              p9 = getValue "p9" new_params_output_string
              params' = [("p0", p0), ("p1", p1), ("p2", p2), ("p3", p3), ("p4", p4), ("p5", p5), ("p6", p6), ("p7", p7), ("p8", p8), ("p9", p9)]
              -}
              currentIter = iterations p
        --putStrLn $ "Solved Params: " ++ show params'
        --putStrLn $ "Previous params: " ++ show (params p)
          cegisLoop p { previous_b = Just c1,
                        previous_q = Just c2,
                        iterations = currentIter - 1,
                        bcxs = bcxs',
                        qcxs = qcxs',
                        qcxs2 = qcxs2',
                        params = params'
                        } spec

unsatResp :: Response -> Bool
unsatResp (Response _ []) = True
unsatResp _               = False

createParameterBall :: [(String, Double)] -> Double -> String
createParameterBall a eps = "(assert (> "++ (createParameterSum a)++ " "++ "1" ++ "))"

createParameterSum :: [(String, Double)] -> String
createParameterSum [(a,b)] = "(norm (- "++ a ++" "++ show b ++ "))"
createParameterSum (x:xs) = "(+ " ++ (createParameterSum [x]) ++ " " ++ (createParameterSum xs) ++ ")"

addAllPhis :: Params -> CompleteSpec -> [(Double, Double, Double)] -> IO ()
addAllPhis p spec cxs = do
  str <- addAllPhis' spec (paramTempFile p) (length cxs) cxs
  let parameterBalls = (createParameterBall (params p) (synthesisPrecision p))
  let phis = unlines (parameterBalls : str) --fmap
  s <- readFile (paramConstantFile p)
  --putStrLn $ "PHIS:\n" ++ phis
  let s_i = replace "counterexamples" phis s
  writeFile (paramCompleteFile p) s_i

addAllPhis' :: CompleteSpec -> String -> Int -> [(Double, Double, Double)] -> IO [String]
addAllPhis' spec file k [x] = do s <- createPhi spec file x (show k)
                                 return [s]
addAllPhis' spec file n (x:xs) = do s <- createPhi spec file x (show n)
                                    s' <- addAllPhis' spec file (n - 1) xs
                                    return $ s : s'

createPhi :: CompleteSpec -> String -> (Double, Double,Double) -> String -> IO String
createPhi spec file (c1,c2,c3) name = do
  s <- readFile file
  -- TODO: automate this
  let andTerm = "(assert (and (= bc " ++ (Numeric.showFFloat Nothing c1 "") ++ ") (= s0_qc " ++ (Numeric.showFFloat Nothing c2 "") ++ ") (= s1_qc " ++ (Numeric.showFFloat Nothing c3 "") ++ ")))"
      s_i = replace "batteryvalue" andTerm s
      -- TODO: automate this
      vars = _vars spec
      variables = tail (_xvars vars) ++ _bvars vars ++ _expanded_qvars vars ++ _tvars vars ++ _cx_vars vars ++ ["choice"]
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
getCX :: String -> String -> String -> Response -> Maybe (Double, Double, Double)
getCX _ _ _ (Response _ []) = Nothing
getCX s1 s2 s3 (Response r vs) = case lookup s1 vs of
  Nothing -> Nothing
  Just x -> case lookup s2 vs of
    Nothing -> Nothing
    Just y -> case lookup s3 vs of
      Nothing -> Nothing
      Just z -> Just (x, y, z)

getValue :: String -> Response -> Double
getValue s (Response r vs) = (fromList vs) ! s

--findCXBalls :: [Double] -> [Double] -> Double -> Double -> Double -> (Double, Double)
--findCXBalls [] [] x y _ = (x,y)
--findCXBalls []

findAllCXBalls :: Double -> [(Double, Double, Double)] -> [Pred]
findAllCXBalls epsilon = fmap (findCXBall epsilon)

findCXBall :: Double -> (Double, Double, Double) -> Pred
--findCXBall x y epsilon = (bi - x)^2 + (qi - y)^2 <= epsilon^2
findCXBall epsilon (x, y, z) = Expr $ EBin Geq (EBin Pow (ERealLit epsilon) (ERealLit 2)) (EBin Plus (EBin Plus (EBin Pow (EBin Minus (EVar "bi") (ERealLit x)) (ERealLit 2)) (EBin Pow (EBin Minus (EVar "s0_qi") (ERealLit y)) (ERealLit 2))) (EBin Pow (EBin Minus (EVar "s1_qi") (ERealLit z)) (ERealLit 2)))

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

-- Entry point
main :: IO ()
main = do
  conf <- readConfig "config/solver.cfg"
  args <- cmdArgsRun mode
  case args of
    (Args file iters precision delta v b q) -> do
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
            params = [], -- updated in prepareTemplates
            previous_b = Nothing,
            previous_q = Nothing,
            verboseMode = v,
            solverConfig = conf
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
          p <- cegisLoop ps spec
          case p of
            Nothing -> putStrLn "Synthesis error"
            Just pr -> do
              putStrLn $ case pr of
                (_, False) -> "\nThe given system is unverifiable in " ++ show iters ++ " iterations"
                (ps, True)  -> "\nSynthesized a program with the following parameters: \n" ++ unlines (fmap printParam ps) ++
                  "\nAnd the following invariant:\n" ++ "b >= " ++ show (snd (head ps)) ++ "\nq <= " ++ show (snd (head (tail ps)))
              removeFile (templateFile synthesisParams)
              removeFile (paramTempFile synthesisParams)
              removeFile (paramConstantFile synthesisParams)
              removeFile (paramCompleteFile synthesisParams)
              --comment out the above to keep the smt2 files for reference.


-- Create uav_dreal_template.smt2
writeTemplate :: Params -> CompleteSpec -> IO ()
writeTemplate p spec = do
  let f = templateFile p
      smt = initializeSMT spec
      charge = printCharge "charge" spec
      flyto = printFlyTo "fly_to" spec
      collect = printCollect "download" spec
      flyfrom = printFlyFrom "fly_back" spec
  writeFile f (unlines (smt ++ charge ++ flyto ++ collect ++ flyfrom ++ initGoal spec ++ endSMT))

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

{-
testWrite :: String -> String -> IO ()
testWrite infile outfile = do
  x <- parseFromFile parseDecls infile
  case x of
    Left e -> error $ show e
    Right decls -> do
      let spec = finishSpec decls
      writeTemplate outfile spec
-}
