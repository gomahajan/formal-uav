module UAV where

import Logic
import Parser
import SMTSolver



{- Algorithm: We ask dReach the following question: Starting from region specified by constraints,
is it possible to end in a state not specified by the constraints?
If dReach says yes, then we have found a region which is safe/stable wrt battery and queue size.
Otherwise, we add the counterexample and its implied space to the constraints.
-}
-- TODO: Update the checkConstraint implementation to call dReach.
checkConstraint :: Pred -> (Double, Double)
checkConstraint p = (100, 0)

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

test :: IO (Either Exception Response) -> IO ()
test inp = do
  r <- inp
  case r of
    (Left e) -> putStr $ show e
    (Right resp) -> putStr $ show resp

-- Extract Counterexample from solver response
getCX :: String -> String -> Response -> Maybe (Double, Double)
getCX _ _ (Response _ []) = Nothing
getCX s1 s2 (Response r vs) = case lookup s1 vs of
  Nothing -> Nothing
  Just x -> case lookup s2 vs of
    Nothing -> Nothing
    Just y -> Just (x,y)

main :: IO ()
main = do
  resp <- run
  putStr $ show resp
