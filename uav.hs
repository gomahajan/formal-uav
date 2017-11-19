data Variable = B | 
                Q deriving (Show)

data Constraint = True |
                  False |
                  LessThanEqual Variable Double | 
                  GreaterThanEqual Variable Double |
                  And Constraint Constraint |
                  Or Constraint Constraint deriving (Show)

-- TODO: Update the checkConstraint implementation to call SMT solver 
checkConstraint :: Constraint -> (Double, Double)
checkConstraint constraint = (100, 0)

updateConstraint :: (Double, Double) -> Constraint -> Constraint
updateConstraint (b,q) constraint = Or (And (GreaterThanEqual B b) (LessThanEqual Q q)) constraint

solve :: Int -> Constraint -> Constraint
solve n constraint 
        | n > 0     = solve (n-1) constraint' 
        | otherwise = constraint
        where constraint' = updateConstraint (checkConstraint constraint) constraint