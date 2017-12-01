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
  iterations :: Int,
  synthesisPrecision :: Double,
  solverPrecision :: Double
} deriving (Show, Eq)


{- Algorithm: We ask dReal the following question: Starting from region specified by constraints,
is it possible to end in a state not specified by the constraints?
If dReal says no, then we have found a region which is safe/stable wrt battery and queue size.

Otherwise, it gives us counterexample bi,qi. We ask another question to dReal, starting from bi,qi
and other examples, find parameters for invariant and program which work. And this continues.
-}
checkConstraint :: Params -> IO (Maybe (Double, Double))
checkConstraint p = do
  let constr = printConstraint' (constraint p)
      constraint_i = replace "q" "qi" (replace "b" "bi" constr)
      constraint_g = replace "q" "q3" (replace "b" "b3" constr)
  addConstraints p constraint_i constraint_g
  output <- run (completeFile p) (solverPrecision p)
  resp <- Main.read output
  return $ getCX "b3" "q3" resp

{- Adds the counterexample and its implied space to the constraints -}
updateConstraint :: (Double, Double) -> Pred -> Pred
--updateConstraint (b,q) = Or (And (Expr $ EBin Geq (EVar "b") (ERealLit b)) (Expr $ EBin Leq (EVar "q") (ERealLit q)))
updateConstraint (b,q) _ = And (Expr $ EBin Eq (EVar "b") (ERealLit b)) (Expr $ EBin Eq (EVar "q") (ERealLit q))

{- Tries to find the safe invariant in given integral steps -}
genInvt :: Params -> IO (Maybe (Pred, Bool))
genInvt p = do
    c <- checkConstraint p
    --putStrLn tf
    let n = iterations p
        pr = case n of
          0 -> return $ Just (constraint p, False)
          n -> case c of
            Nothing -> return $ Just (constraint p, True)
            Just cx -> trace (show cx) $ genInvt p{ iterations = n - 1, constraint = updateConstraint cx (constraint p) }
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
    Just y -> Just $ adjustCX x y

adjustCX :: Double -> Double -> (Double, Double)
adjustCX x y = (fromIntegral (round (x * 10)) / 10.0, fromIntegral (round (y * 10)) / 10.0)
  {-case (mod (truncate (x * 10)) 10, mod (truncate (y * 10)) 10) of
  (0, 0) -> (round x, round y)
  (0, _) -> (round x, y)
  (_, 0) -> (x, round y)
  _      -> (x, y) -}

-- Create SMT with new constraints. Also overwrites if it already exists --
addConstraints :: Params -> String -> String -> IO ()
addConstraints p constraintI constraintG = do
  --s <- readFile "uav_dreal.smt2"
  s <- readFile (templateFile p)
  let s_i = replace "constraintI" constraintI s
  let s_i_g  = replace "constraintG" constraintG s_i
  writeFile (completeFile p) s_i_g

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
          initp = And (Expr (EBin Geq (EVar "b") (ERealLit 100))) (Expr (EBin Leq (EVar "q") (ERealLit 20)))
          synthesisParams = Params {
            constraint = initp,
            completeFile = cmpf,
            templateFile = tmpf,
            iterations = iters,
            synthesisPrecision = precision,
            solverPrecision = delta
          }
      p <- genInvt synthesisParams
      case p of
        Nothing -> putStrLn "Nothing"
        Just pr -> putStrLn $ case pr of
          (_, False) -> "The given system is unverifiable in " ++ show iters ++ " iterations"
          (p, True)  -> "The given system is provably safe with the following loop invariant: " ++ printConstraint' p
