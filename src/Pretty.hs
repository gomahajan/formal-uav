module Pretty where

import Data.Char
import Data.Ratio

import Logic


printConstraint :: Pred -> String
printConstraint p = "(assert " ++ printConstraint' p ++ ")"

printConstraint' :: Pred -> String
printConstraint' (Lit b)     = map toLower (show b)
printConstraint' (Expr e)    = printE e
printConstraint' (And ps) = "(and " ++ unwords (map printConstraint' ps) ++ ")"
printConstraint' (Or ps)  = "(or " ++ unwords (map printConstraint' ps) ++ ")"
printConstraint' (Not p)     = "(not " ++ printConstraint' p ++ ")"
printConstraint' (Impl p1 p2) = "(=> " ++ printConstraint' p1 ++ " " ++ printConstraint' p2 ++ ")"


printE :: Exp -> String
printE (EStrLit s)     = s
--printE (ERealLit x)    =  "(/ " ++ show n ++ " " ++ show d ++ ")"
--  where r = toRational x
--        n = numerator r
--        d = denominator r
printE (ERealLit x)    =  show x
printE (EUOp op e)     = "(" ++ printUOp op ++ " " ++ printE e ++ ")"
printE (EBin op e1 e2) = "(" ++ printBOp op ++ " " ++ printE e1 ++ " " ++ printE e2 ++ ")"
printE (EVar s)        = s

printUOp :: UnOp -> String
printUOp Neg = "-"

printBOp :: BinOp -> String
printBOp Lt = "<"
printBOp Gt = ">"
printBOp Leq = "<="
printBOp Geq = ">="
printBOp Plus = "+"
printBOp Times = "*"
printBOp Div = "/"
printBOp Eq = "="
printBOp Pow = "^"
printBOp Minus = "-"
