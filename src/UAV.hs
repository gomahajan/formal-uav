{-# LANGUAGE DeriveDataTypeable #-}

module Main where

import System.IO
import Data.String.Utils
import System.Environment
import Debug.Trace
import System.Console.CmdArgs
import Data.Map (fromList, (!))

import Logic
import Parser
import SMTSolver
import Pretty

programName = "TBD"
versionName = "0.0"

{- Command Line Args -}


{-# ANN module "HLint: ignore Use camelCase" #-}

data CommandLineArgs = Args {
  smt_file :: String, -- file prefix
  depth :: Int,
  precision :: Double,
  smt_precision :: Double
} deriving (Data, Typeable, Show, Eq)

cargs = Args {
  smt_file      = ""    &= argPos 0,
  depth    = 10    &= help "Maximum number of iterations when running synthesis algorithm.",
  precision     = 0.01  &= help "Precision for hybrid system synthesis.",
  smt_precision = 0.001 &= help "Delta-precision for SMT solver."
}


data Params = Params {
  constraint :: Pred,
  completeFile :: String,
  templateFile :: String,
  paramTempFile :: String,
  paramCompleteFile :: String,
  iterations :: Int,
  synthesisPrecision :: Double,
  solverPrecision :: Double,
  bcxs :: [Double],
  qcxs :: [Double],
  qcxs2 :: [Double],
  params :: [(String, Double)],
  previous_b :: Maybe Double, -- could rename to previous counter-example
  previous_q :: Maybe Double
} deriving (Show, Eq)


{- Algorithm: We ask dReal the following question: Starting from region specified by constraints,
is it possible to end in a state not specified by the constraints?
If dReal says no, then we have found a region which is safe/stable wrt battery and queue size.

Otherwise, it gives us counterexample bi,qi. We ask another question to dReal, starting from bi,qi
and other examples, find parameters for invariant and program which work. And this continues.
-}

{- Add constraintI, constraintG
   add parameter p2,p3
   run dreal, ask for counter example bc,qc from uav_dreal_template.smt2
   update constraint using p0,p1,p2,p3
   add constraint
   using counterexample, build b (or currentbs (= bi bc))
   using counterexample, build q (or currentqs (= qi qc))
   run dreal, ask for p which work, and continue
-}
cegisLoop :: Params -> IO (Maybe ([(String, Double)], Bool))
cegisLoop p =
  if iterations p <= 0
  then return $ Just (params p, False)
  else do
    let paramStr = unlines (fmap (printConstraint . Expr) (zipWith (EBin Eq) (fmap (EStrLit . fst) (params p)) (fmap (ERealLit . snd) (params p))))
        balls = findAllCXBalls (synthesisPrecision p) (zip3 (bcxs p) (qcxs p) (qcxs2 p))
        ballStr = case balls of
          [] -> ""
          bs -> printConstraint (And (fmap Not bs))
    addParams (paramStr ++ "\n" ++ ballStr) (templateFile p) (completeFile p)
    output <- run (completeFile p) (solverPrecision p)
    resp <- Main.read output
    let cxs = getCX "bi" "s1_qi" "s2_qi" resp
    --putStrLn $ "Original cx: " ++ show cxs
    case cxs of
      Nothing -> return $ Just (params p, True)
      Just (c1, c2, c3) -> do
        let --(c1,c2) = findCXBall (previous_b p) (previous_q p) c1_naive c2_naive (synthesisPrecision p)
            bcxs' = c1 : bcxs p
            qcxs' = c2 : qcxs p
            qcxs2' = c3 : qcxs2 p
            -- TODO: convert battery queue lists to (battery,queue) list
            constraintbq = "(assert (=> (and (and (>= bi p0) (<= qi p1)) constraintbq) (and (> b0 0) (> b1 0) (> b2 0) (> b3 0) (< q0 100) (< q1 100) (< q2 100) (< q3 100) (and (>= b3 p0) (<= q3 p1)))))"
            -- replace "constraintbq" with
            -- battery_constraint = printConstraint $ generateVarConstraints "bi" "qi" bcxs' qcxs'
            --battery_constraint = unlines $ fmap (((flip (replace "constraintbq")) constraintbq) . printConstraint') (zipWith (findCXBall (synthesisPrecision p)) bcxs' qcxs')
        --putStrLn $ "bcxs: " ++ show bcxs'
        --putStrLn $ "qcxs: " ++ show qcxs'
        --putStrLn $ "cx: " ++ show (c1, c2, c3)
        addAllPhis $ zip3 bcxs' qcxs' qcxs2'
        new_params_output <- run (paramCompleteFile p) (solverPrecision p)
        new_params_output_string <- Main.read new_params_output
        let p0 = getValue "p0" new_params_output_string
            p1 = getValue "p1" new_params_output_string
            p2 = getValue "p2" new_params_output_string
            p3 = getValue "p3" new_params_output_string
            p4 = getValue "p4" new_params_output_string
            p5 = getValue "p5" new_params_output_string
            p6 = getValue "p6" new_params_output_string
            p7 = getValue "p7" new_params_output_string
            p8 = getValue "p8" new_params_output_string
            p9 = getValue "p9" new_params_output_string
            currentIter = iterations p
            params' = [("p0", p0), ("p1", p1), ("p2", p2), ("p3", p3), ("p4", p4), ("p5", p5), ("p6", p6), ("p7", p7), ("p8", p8), ("p9", p9)]
        putStrLn $ "Solved Params: " ++ show params'
        --putStrLn $ "Previous params: " ++ show (params p)
        cegisLoop p { previous_b = Just c1,
                      previous_q = Just c2,
                      iterations = currentIter - 1,
                      bcxs = bcxs',
                      qcxs = qcxs',
                      qcxs2 = qcxs2',
                      params = params'
                      }

{-
  addParameters p0 p1 p2 p3 --initial 100 0 20 4
  bc qc = run uav_dreal_complete.smt2
  updateConstraint p0 p1
  addConstraints
  updateBatteryAndQueue oldbs oldqs bc qc
  addBatteryAndQueue
  p0 p1 p2 p3 = run uav_dreal_parameter_complete.smt2
  cegisLoop p' -}

addAllPhis :: [(Double, Double, Double)] -> IO ()
addAllPhis cxs = do
  str <- addAllPhis' (length cxs) cxs
  let phis = unlines str --fmap
  s <- readFile "smt/uav_dreal_parameter_constant_template.smt2"
  let s_i = replace "counterexamples" phis s
  writeFile "smt/uav_dreal_parameter_complete.smt2" s_i

addAllPhis' :: Int -> [(Double, Double, Double)] -> IO [String]
addAllPhis' k [x] = do s <- createPhi x (show k)
                       return [s]
addAllPhis' n (x:xs) = do s <- createPhi x (show n)
                          s' <- addAllPhis' (n - 1) xs
                          return $ s : s'

createPhi :: (Double, Double, Double) -> String -> IO String
createPhi (c1,c2,c3) name = do
  s <- readFile "smt/uav_dreal_parameter_template.smt2"
  let s_i = replace "batteryvalue" (printConstraint (generateAndTerm3 "bc" "s1_qc" "s2_qc" c1 c2 c3)) s
      variables = ["x0", "x1", "x2", "x3", "bi", "b0", "b1", "b2", "b3", "s1_qi", "s1_q0", "s1_q1", "s1_q2", "s1_q3", "s2_qi", "s2_q0", "s2_q1", "s2_q2", "s2_q3", "t0", "t1", "t2", "t3", "bc", "s1_qc", "s2_qc", "choice"]
      s_i_g = foldl (\str v -> (replace v (v ++ "_" ++ name) str)) s_i variables
  -- for each variable, replace variable in s_i with variable++_++id
  return s_i_g

{- Adds the counterexample and its implied space to the constraints -}
updateConstraint :: (Double, Double) -> Pred -> Pred
--updateConstraint (b,q) = Or (And (Expr $ EBin Geq (EVar "b") (ERealLit b)) (Expr $ EBin Leq (EVar "q") (ERealLit q)))
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
read :: String -> IO Response
read src = return $ parseDRealSat src


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
findCXBall epsilon (x, y, z) = Expr $ EBin Geq (EBin Pow (ERealLit epsilon) (ERealLit 2)) (EBin Plus (EBin Plus (EBin Pow (EBin Minus (EVar "bi") (ERealLit x)) (ERealLit 2)) (EBin Pow (EBin Minus (EVar "s1_qi") (ERealLit y)) (ERealLit 2))) (EBin Pow (EBin Minus (EVar "s2_qi") (ERealLit z)) (ERealLit 2)))

getTheta :: Double -> Double -> Double
getTheta y x = if x == 0
               then (pi / 2)
               else atan (y/x)

--phi :: Double -> Double -> String


-- Create SMT with new constraints. Also overwrites if it already exists --
addConstraints :: String -> String -> String -> String -> IO ()
addConstraints tmpf cmpf constraintI constraintG = do
  --s <- readFile "uav_dreal.smt2"
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


main :: IO ()
main = do
  args <- cmdArgsRun mode
  case args of
    (Args file iters precision delta) -> do
      let tmpf = file ++ "_template.smt2"
          cmpf = file ++ "_complete.smt2"
          paramtf = file ++ "_parameter_template.smt2"
          paramcf = file ++ "_parameter_complete.smt2"
          initp = And [Expr (EBin Geq (EVar "b") (ERealLit 100)), Expr (EBin Leq (EVar "q") (ERealLit 20))]
          synthesisParams = Params {
            constraint = initp,
            completeFile = cmpf,
            templateFile = tmpf,
            paramTempFile = paramtf,
            paramCompleteFile = paramcf,
            iterations = iters,
            synthesisPrecision = precision,
            solverPrecision = delta,
            bcxs = [],
            qcxs = [],
            qcxs2 = [],
            params = [("p0",9), ("p1",30), ("p2",10), ("p3",9), ("p4",10), ("p5",30), ("p6",30), ("p7",10), ("p8",10), ("p9",2)],
            previous_b = Nothing,
            previous_q = Nothing
          }
      p <- cegisLoop synthesisParams
      putStrLn $ show p
      {-case p of
        Nothing -> putStrLn "Nothing"
        Just pr -> putStrLn $ case pr of
          (_, False) -> "The given system is unverifiable in " ++ show iters ++ " iterations"
          (p, True)  -> "The given system is provably safe with the following loop invariant: " ++ printConstraint' p -}
