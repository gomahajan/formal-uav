data Variable = B | 
                Q deriving (Show)

data Constraint = True |
                  False |
                  LessThanEqual Variable Double | 
                  GreaterThanEqual Variable Double |
                  And Constraint Constraint |
                  Or Constraint Constraint deriving (Show)

{- Algorithm: We ask dReach the following question: Starting from region specified by constraints,
is it possible to end in a state not specified by the constraints? 
If dReach says yes, then we have found a region which is safe/stable wrt battery and queue size.
Otherwise, we add the counterexample and its implied space to the constraints. 
-}
-- TODO: Update the checkConstraint implementation to call dReach.
checkConstraint :: Constraint -> (Double, Double)
checkConstraint constraint = (100, 0)

{- Adds the counterexample and its implied space to the constraints -}
updateConstraint :: (Double, Double) -> Constraint -> Constraint
updateConstraint (b,q) constraint = Or (And (GreaterThanEqual B b) (LessThanEqual Q q)) constraint

solve :: Int -> Constraint -> Constraint
solve n constraint 
        | n > 0     = solve (n-1) constraint' 
        | otherwise = constraint
        where constraint' = updateConstraint (checkConstraint constraint) constraint