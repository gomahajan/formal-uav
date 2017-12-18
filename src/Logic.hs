{-# LANGUAGE GADTs #-}

module Logic where

import Text.Parsec
import Data.Map
import Control.Monad.Except

type Counterexample = (Double, Double)

-- Environment
type Env = Map String Exp

data SpVar = B | Q deriving (Eq, Show)

data Val where
  VLit  :: String -> Val -- Special variable (b, q, etc)
  VReal :: Double -> Val
  VBool :: Bool -> Val
  deriving (Eq, Show)

-- Binary Operations
data BinOp =
  Lt | Gt | Leq | Geq | Plus | Minus | Times | Div | Eq | Pow
  deriving (Ord, Eq, Show)

-- Unary operations
data UnOp =
  Neg | Sin | Cos | Tan
  deriving (Ord, Eq, Show)

-- Expressions: real-valued
data Exp where
  EStrLit :: String -> Exp
  ERealLit :: Double -> Exp
  EUOp :: UnOp -> Exp -> Exp
  EBin :: BinOp -> Exp -> Exp -> Exp
  EVar :: String -> Exp
  deriving (Eq, Show)

{- Currently unused!!
eval :: Env -> Exp -> Maybe Val
eval env (EStrLit s) = Just $ VLit s
eval env (ERealLit x) = Just $ VReal x
eval env (EUOp op e) = evalUOp op (eval env e)
eval env (EBin Eq e1 e2) = evalArithBool (==) (eval env e1) (eval env e2)
eval env (EBin Lt e1 e2) = evalArithBool (<) (eval env e1) (eval env e2)
eval env (EBin Gt e1 e2) = evalArithBool (>) (eval env e1) (eval env e2)
eval env (EBin Leq e1 e2) = evalArithBool (<=) (eval env e1) (eval env e2)
eval env (EBin Geq e1 e2) = evalArithBool (>=) (eval env e1) (eval env e2)
eval env (EBin Plus e1 e2) = evalNumeric (+) (eval env e1) (eval env e2)
eval env (EBin Minus e1 e2) = evalNumeric (-) (eval env e1) (eval env e2)
eval env (EBin Times e1 e2) = evalNumeric (*) (eval env e1) (eval env e2)
eval env (EBin Pow e1 e2) = evalNumeric (**) (eval env e1) (eval env e2)
eval env (EBin Div e1 e2) = evalNumeric (/) (eval env e1) (eval env e2)
eval env (EVar s) = case Data.Map.lookup s env of
  Just e  -> eval env e
  Nothing -> Nothing

evalUOp :: UnOp -> Maybe Val -> Maybe Val
evalUOp Neg (Just (VReal x)) = Just $ VReal (-x)
evalUOp Neg _         = Nothing

evalNumeric ::(Double -> Double -> Double) -> Maybe Val -> Maybe Val -> Maybe Val
evalNumeric op v1 v2 = case (v1, v2) of
  (Just (VReal x), Just (VReal y)) -> Just $ VReal $ op x y
  _                  -> Nothing


evalArithBool :: (Double -> Double -> Bool) -> Maybe Val -> Maybe Val -> Maybe Val
evalArithBool op x y = case (x, y) of
  (Just (VReal x), Just (VReal y)) -> Just $ VBool $ op x y
  _                                -> Nothing

-}
data Pred = Lit Bool
  | Expr Exp
  | And [Pred]
  | Or [Pred]
  | Not Pred
  | Impl Pred Pred
  deriving (Eq, Show)

{- Currently unused!
-- Checks that predicate is well formed (ie all terms are booleans)
checkPred :: Env -> Pred -> Bool
checkPred _ (Lit b) = True
checkPred env (Expr e) = case eval env e of
  Just (VBool b) -> True
  _              -> False
checkPred env (And []) = True
checkPred env (And (e:es)) = checkPred env e && checkPred env (And es)
checkPred env (Or []) = True
checkPred env (Or (e:es))  = checkPred env e && checkPred env (And es)
checkPred env (Not e)     = checkPred env e

data Exception = NumArgs Integer [Val]
               | TypeMismatch String Val
               | Parser ParseError
               | BadSpecialForm String Val
               deriving (Eq, Show)

type ThrowsError = Either Exception
-}
