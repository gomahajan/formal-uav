module Main where

import System.IO
import Data.String.Utils
import System.Environment

import Logic
import Parser
import SMTSolver
import Pretty



{- Algorithm: We ask dReal the following question: Starting from region specified by constraints,
is it possible to end in a state not specified by the constraints?
If dReal says no, then we have found a region which is safe/stable wrt battery and queue size.
Otherwise, we add the counterexample and its implied space to the constraints.
-}
checkConstraint :: String -> String -> Pred -> IO (Maybe (Double, Double))
checkConstraint tmpf outf p = do
  let constraint = printConstraint' p
      constraint_i = replace "q" "qi" (replace "b" "bi" constraint)
      constraint_g = replace "q" "q3" (replace "b" "b3" constraint)
  addConstraints tmpf outf constraint_i constraint_g
  output <- run
  resp <- Main.read output
  return $ getCX "b3" "q3" resp

{- Adds the counterexample and its implied space to the constraints -}
updateConstraint :: (Double, Double) -> Pred -> Pred
updateConstraint (b,q) = Or (And (Expr $ EBin Geq (EVar "B") (ERealLit b)) (Expr $ EBin Leq (EVar "Q") (ERealLit q)))

{- Tries to find the safe invariant in given integral steps -}
genInvt :: String -> String -> Int -> Pred -> IO (Maybe (Pred, Bool))
genInvt tf cf n constraint = do
    c <- checkConstraint tf cf constraint
    let pr = case n of
          0 -> return $ Just (constraint, False)
          n -> case c of
            Nothing -> return $ Just (constraint, True)
            Just cx -> genInvt tf cf (n-1) (updateConstraint cx constraint)
    pr

-- Read solver response
read :: String -> IO Response
read src = do
  resp <- readFile src
  --putStr $ show resp
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
  let (filename, iters) = case args of
       [] -> error "Please provide an smt file"
       (x:xs) -> case xs of
              [] -> (x, 10)
              (y:ys) -> (x, Prelude.read y)
      tmpf = filename ++ "_template.smt2"
      cmpf = filename ++ "_complete.smt2"
      initp = (And (Expr (EBin Geq (EVar "bi") (ERealLit 100))) (Expr (EBin Leq (EVar "qi") (ERealLit 0))))
  p <- genInvt tmpf cmpf iters initp
  case p of
    Nothing -> putStr "Nothing"
    Just pr -> putStr $ case pr of
      (_, False) -> "The given system is unverifiable in " ++ show iters ++ " iterations"
      (p, True)  -> "The given system is provably safe with the following loop invariant: " ++ printConstraint' p
