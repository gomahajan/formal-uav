module Main where

import System.IO
import Data.String.Utils
import System.Environment
import Debug.Trace

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
  output <- run outf
  resp <- Main.read output
  return $ getCX "b3" "q3" resp

{- Adds the counterexample and its implied space to the constraints -}
updateConstraint :: (Double, Double) -> Pred -> Pred
--updateConstraint (b,q) = Or (And (Expr $ EBin Geq (EVar "b") (ERealLit b)) (Expr $ EBin Leq (EVar "q") (ERealLit q)))
updateConstraint (b,q) _ = And (Expr $ EBin Eq (EVar "b") (ERealLit b)) (Expr $ EBin Eq (EVar "q") (ERealLit q))

{- Tries to find the safe invariant in given integral steps -}
genInvt :: String -> String -> Int -> Pred -> IO (Maybe (Pred, Bool))
genInvt tf cf n constraint = do
    c <- checkConstraint tf cf constraint
    --putStrLn tf
    let pr = case n of
          0 -> return $ Just (constraint, False)
          n -> case c of
            Nothing -> return $ Just (constraint, True)
            Just cx -> trace (show cx) $ genInvt tf cf (n-1) (updateConstraint cx constraint)
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
addConstraints :: String -> String -> String -> String -> IO ()
addConstraints templateFile completeFile constraintI constraintG = do
  --s <- readFile "uav_dreal.smt2"
  s <- readFile templateFile
  let s_i = replace "constraintI" constraintI s
  let s_i_g  = replace "constraintG" constraintG s_i
  writeFile completeFile s_i_g

--roundn :: Num a => Int -> a -> a
--roundn n x = (fromInteger $ round $ x * (10^n)) / (10.0^^n)

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
      initp = And (Expr (EBin Geq (EVar "b") (ERealLit 100))) (Expr (EBin Leq (EVar "q") (ERealLit 20)))
  p <- genInvt tmpf cmpf iters initp
  case p of
    Nothing -> putStrLn "Nothing"
    Just pr -> putStrLn $ case pr of
      (_, False) -> "The given system is unverifiable in " ++ show iters ++ " iterations"
      (p, True)  -> "The given system is provably safe with the following loop invariant: " ++ printConstraint' p
