module Pretty where

import Data.Char
import Data.Ratio

import Logic


printConstraint :: Env -> Pred -> String
printConstraint e p = "(assert " ++ printConstraint' e p ++ ")"

printConstraint' :: Env -> Pred -> String
printConstraint' _ (Lit b)     = map toLower (show b)
printConstraint' env (Expr e)    = printE env e
printConstraint' env (And ps) = "(and " ++ unwords (map (printConstraint' env) ps) ++ ")"
printConstraint' env (Or ps)  = "(or " ++ unwords (map (printConstraint' env) ps) ++ ")"
printConstraint' env (Not p)     = "(not " ++ printConstraint' env p ++ ")"
printConstraint' env (Impl p1 p2) = "(=> " ++ printConstraint' env p1 ++ " " ++ printConstraint' env p2 ++ ")"


printE :: Env -> Exp -> String
printE env (EStrLit s)     = case lookup s env of
  Nothing -> s
  Just p -> printConstraint' env p
--printE (ERealLit x)    =  "(/ " ++ show n ++ " " ++ show d ++ ")"
--  where r = toRational x
--        n = numerator r
--        d = denominator r
printE _ (ERealLit x)    =  show x
printE env (EUOp op e)     = "(" ++ printUOp op ++ " " ++ printE env e ++ ")"
printE env (EBin op e1 e2) = "(" ++ printBOp op ++ " " ++ printE env e1 ++ " " ++ printE env e2 ++ ")"
printE env (EVar s)        = case lookup s env of
  Nothing -> s
  Just p -> printConstraint' env p

printUOp :: UnOp -> String
printUOp Neg  = "-"
printUOp UNot = "not"
printUOp Sin  = "sin"
printUOp Cos  = "cos"
printUOp Tan  = "tan"

printBOp :: BinOp -> String
printBOp Lt    = "<"
printBOp Gt    = ">"
printBOp Leq   = "<="
printBOp Geq   = ">="
printBOp Plus  = "+"
printBOp Times = "*"
printBOp Div   = "/"
printBOp Eq    = "="
printBOp Pow   = "^"
printBOp Minus = "-"
