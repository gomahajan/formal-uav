data Variable = B | 
                Q deriving (Show)

data Constraint = True |
                  False |
                  LessThanEqual Variable Double | 
                  GreaterThanEqual Variable Double |
                  And Constraint Constraint |
                  Or Constraint Constraint deriving (Show)

updateConstraint :: (Double, Double) -> Constraint -> Constraint
updateConstraint (b,q) constraint = Or (And (GreaterThanEqual B b) (LessThanEqual Q q)) constraint