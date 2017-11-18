data Variable = B | 
                Q

data Constraint = True |
                  False |
                  LessThan Variable Double | 
                  GreaterThan Variable Double |
                  And Constraint Constraint |
                  Or Constraint Constraint

updateConstraint :: (Double, Double) -> Constraint -> Constraint
updateConstraint (b,q) constraint = And (And (GreaterThan B b) (LessThan Q q)) constraint