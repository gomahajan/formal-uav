{-# LANGUAGE DeriveDataTypeable #-}

module Main where

import System.IO
import Data.String.Utils
import System.Environment
import Debug.Trace
import System.Console.CmdArgs

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
  params :: [(String, Double)],
  previous_b :: Double, -- could rename to previous counter-example
  previous_q :: Double
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
cegisLoop :: Params -> IO (Maybe (Pred, Bool))
cegisLoop p =
  if iterations p <= 0
  then return $ Just (constraint p, False)
  else do
    let constr = printConstraint' (constraint p)
        constraint_i = replace "q" "qi" (replace "b" "bi" constr)
        constraint_g = replace "q" "q3" (replace "b" "b3" constr)
        paramStr = unlines (fmap (printConstraint . Expr) (zipWith (EBin Eq) (fmap (EStrLit . fst) (params p)) (fmap (ERealLit . snd) (params p))))
    addConstraints (templateFile p) (completeFile p) constraint_i constraint_g --initial false
    addParams paramStr (completeFile p)
    output <- run (completeFile p) (solverPrecision p)
    resp <- Main.read output
    let cxs = getCX "bi" "qi" resp
        const' =  Or [constraint p, And [Expr (EBin Geq (EStrLit "b") (ERealLit (snd (head (params p))))), Expr (EBin Leq (EStrLit "q") (ERealLit (snd (head (tail (params p))))))]]
        constr' = printConstraint' const'
        paramConst_i = replace "q" "qi" (replace "b" "bi" constr')
        paramConst_g = replace "q" "q3" (replace "b" "b3" constr')

    case cxs of
      Nothing -> return $ Just (const', True)
      Just (c1_naive, c2_naive) -> do
        addConstraints (paramTempFile p) (paramCompleteFile p) paramConst_i paramConst_g
        let (c1,c2) = findCXBall (previous_b p) (previous_q p) c1_naive c2_naive (synthesisPrecision p)
            bcxs' = c1 : bcxs;
            qcxs' = c2 : qcxs;
        -- TODO: add battery,queue to smt
        new_params_output <- run (paramCompleteFile p) (solverPrecision p)
        new_params_output_string <- Main.read new_params_output
        let p0 = getValue "p0" new_params_output_string
            p1 = getValue "p1" new_params_output_string
            p2 = getValue "p2" new_params_output_string
            p3 = getValue "p3" new_params_output_string
            currentIter = iterations p
            params' = [("p0", p0), ("p1", p1), ("p2", p2), ("p3", p3)]
        cegisLoop p { previous_b = c1,
                      previous_q = c2,
                      iterations = currentIter - 1,
                      bcxs = bcxs',
                      qcxs = qcxs',
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



checkConstraint :: Params -> IO (Maybe (Double, Double))
checkConstraint p = do
  let constr = printConstraint' (constraint p)
      constraint_i = replace "q" "qi" (replace "b" "bi" constr)
      constraint_g = replace "q" "q3" (replace "b" "b3" constr)
  addConstraints (templateFile p) (completeFile p) constraint_i constraint_g
  output <- run (completeFile p) (solverPrecision p)
  resp <- Main.read output
  return $ getCX "b3" "q3" resp

{- Adds the counterexample and its implied space to the constraints -}
updateConstraint :: (Double, Double) -> Pred -> Pred
--updateConstraint (b,q) = Or (And (Expr $ EBin Geq (EVar "b") (ERealLit b)) (Expr $ EBin Leq (EVar "q") (ERealLit q)))
updateConstraint (b,q) _ = And [Expr $ EBin Eq (EVar "b") (ERealLit b), Expr $ EBin Eq (EVar "q") (ERealLit q)]

makeEqPred :: String -> Double -> Pred
makeEqPred s v = Expr $ EBin Eq (EVar s) (ERealLit v)

generateVarConstraints :: String -> [Double] -> Maybe Pred
generateVarConstraints s []  = Nothing
generateVarConstraints s [v] = Just $ makeEqPred s v
generateVarConstraints s vs  = Just $ Or (map (makeEqPred s) vs)

{- Tries to find the safe invariant in given integral steps -}
genInvt :: Params -> IO (Maybe (Pred, Bool))
genInvt p = do
    c <- checkConstraint p
    --putStrLn tf
    let bs = bcxs p
        qs = qcxs p
        n = iterations p
        pr = case n of
          0 -> return $ Just (constraint p, False)
          n -> case c of
            Nothing -> return $ Just (constraint p, True)
            Just cx -> trace (show cx) $ genInvt p{ iterations = n - 1, constraint = updateConstraint cx (constraint p), bcxs = fst cx : bs, qcxs = snd cx : qs }
    pr

-- Read solver response
read :: String -> IO Response
read src = return $ parseDRealSat src


-- Extract Counterexample from solver response
getCX :: String -> String -> Response -> Maybe (Double, Double)
getCX _ _ (Response _ []) = Nothing
getCX s1 s2 (Response r vs) = case lookup s1 vs of
  Nothing -> Nothing
  Just x -> case lookup s2 vs of
    Nothing -> Nothing
    Just y -> Just (x, y)

getValue :: String -> Response -> Maybe (Double)
getValue s (Response r vs) = lookup s vs 

findCXBall :: Double -> Double -> Double -> Double -> Double -> (Double, Double)
findCXBall previous_x previous_y x y epsilon =
  if (((x - previous_x) ^ 2 + (y - previous_y) ^ 2) > epsilon ^ 2)
  then (x, y)
  else let theta = getTheta (y - previous_y) (x - previous_x)
           new_x = previous_x + (cos(theta) * epsilon)
           new_y = previous_y + (sin(theta) * epsilon)
       in (new_x, new_y)

getTheta :: Double -> Double -> Double
getTheta y x = if x == 0
               then 0
               else atan (y/x)

-- Create SMT with new constraints. Also overwrites if it already exists --
addConstraints :: String -> String -> String -> String -> IO ()
addConstraints tmpf cmpf constraintI constraintG = do
  --s <- readFile "uav_dreal.smt2"
  s <- readFile tmpf
  let s_i = replace "constraintI" constraintI s
  let s_i_g  = replace "constraintG" constraintG s_i
  writeFile cmpf s_i_g

addParams :: String -> String -> IO ()
addParams ps file = do
  s <- readFile file
  let pstr = replace "parametervalues" ps s
  writeFile file pstr

--roundn :: Num a => Int -> a -> a
--roundn n x = (fromInteger $ round $ x * (10^n)) / (10.0^^n)

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
            params = [("p0",100), ("p1",0), ("p2",20), ("p3",4)],
            previous_b = 100,
            previous_q = 0
          }
      p <- genInvt synthesisParams
      case p of
        Nothing -> putStrLn "Nothing"
        Just pr -> putStrLn $ case pr of
          (_, False) -> "The given system is unverifiable in " ++ show iters ++ " iterations"
          (p, True)  -> "The given system is provably safe with the following loop invariant: " ++ printConstraint' p
