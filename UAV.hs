module Main where

import System.IO
import Data.String.Utils
import System.Environment

import Logic
import Parser
import SMTSolver
import Pretty



{- Algorithm: We ask dReach the following question: Starting from region specified by constraints,
is it possible to end in a state not specified by the constraints?
If dReach says yes, then we have found a region which is safe/stable wrt battery and queue size.
Otherwise, we add the counterexample and its implied space to the constraints.
-}
checkConstraint :: Pred -> IO (Maybe (Double, Double))
checkConstraint p = do
  let constraint = printConstraint' p
  let constraint_i = (replace "q" "qi" (replace "b" "bi" s))
  let constraint_g = (replace "q" "q3" (replace "b" "b3" s))
  addConstraints "uav_dreal_template.smt2" "uav_dreal_complete.smt2" constraint_i constraint_g
  output <- run
  let response = parseSat output
  toCounterExample response

{- Adds the counterexample and its implied space to the constraints -}
updateConstraint :: (Double, Double) -> Pred -> Pred
updateConstraint (b,q) p = Or (And (Expr $ EBin Geq (EVar "B") (ERealLit b)) (Expr $ EBin Leq (EVar "Q") (ERealLit q))) p

solve :: Int -> Pred -> Pred
solve n constraint
        | n > 0     =  case checkConstraint constraint of
          Nothing -> constraint
          Just counterExample -> solve (n-1) (updateConstraint counterExample constraint)
        | otherwise = constraint

-- Read solver response
read :: String -> IO (Either Exception Response)
read src = do
  resp <- readFile src
  putStr $ show resp
  return $ parseSat resp


-- Extract Counterexample from solver response
getCX :: String -> String -> Response -> Maybe (Double, Double)
getCX _ _ (Response _ []) = Nothing
getCX s1 s2 (Response r vs) = case lookup s1 vs of
  Nothing -> Nothing
  Just x -> case lookup s2 vs of
    Nothing -> Nothing
    Just y -> Just (x,y)

-- Create SMT with new constraints. Also overwrites if it already exists --
addConstraints :: String -> String -> String -> String -> IO ()
addConstraints templateFile completeFile constraintI constraintG = do
  --s <- readFile "uav_dreal.smt2"
  s <- readFile templateFile
  let s_i = replace "constraintI" constraintI s
  let s_i_g  = replace "constraintG" constraintG s_i
  writeFile completeFile s_i_g

main :: IO ()
main = do
  args <- getArgs
  -- Not sure why but I have to indent it like this...
  let (filename, iters) = case args of
                            [] -> error "Please provide an smt file"
                            (x:xs) -> case xs of
                                       [] -> (x, 10)
                                       (y:ys) -> (x, Prelude.read y)
