module UAV where

import Logic
import Parser



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
