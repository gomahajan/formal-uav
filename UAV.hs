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
-- TODO: Update the checkConstraint implementation to call dReach.
-- write string to file, run solver, parse response
-- Make this a maybe!
checkConstraint :: Int -> String -> Pred -> IO (Maybe (Double, Double)) --oe, return updated Maybe Pred and iterate?
--checkConstraint f p = (100, 0)
checkConstraint 0 _ _ = return Nothing
checkConstraint f p = do
  addConstraints f


{- Adds the counterexample and its implied space to the constraints -}
updateConstraint :: (Double, Double) -> Pred -> Pred
updateConstraint (b,q) p = Or (And (Expr $ EBin Geq (EVar "B") (ERealLit b)) (Expr $ EBin Leq (EVar "Q") (ERealLit q))) p

solve :: Int -> Pred -> Pred
solve n constraint
        | n > 0     = solve (n-1) constraint'
        | otherwise = constraint
        where constraint' = updateConstraint (checkConstraint constraint) constraint

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
addConstraints :: String -> String -> String -> IO ()
addConstraints file constraintI constraintG = do
  --s <- readFile "uav_dreal.smt2"
  s <- readFile file
  let s_i = replace "constraintI" constraintI s
  let s_i_g  = replace "constraintG" constraintG s_i
  writeFile file s_i_g

main :: IO ()
main = do
  args <- getArgs
  -- Not sure why but I have to indent it like this...
  let (filename, iters) = case args of
                            [] -> error "Please provide an smt file"
                            (x:xs) -> case xs of
                                       [] -> (x, 10)
                                       (y:ys) -> (x, Prelude.read y)
