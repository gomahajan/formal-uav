{-# LANGUAGE GADTs #-}

module Logic where

import Text.Parsec
import Data.Map
import Control.Monad.Except

-- Environment
type Env = Map String Exp

data SpVar = B | Q

data Val where
  VLit  :: String -> Val -- Special variable (b, q, etc)
  VReal :: Double -> Val
  VBool :: Bool -> Val
  deriving (Eq, Show)

-- Binary Operations
data BinOp =
  Lt | Gt | Leq | Geq | Plus | Times | Div | Eq
  deriving (Eq, Show)

-- Unary operations
data UnOp =
  Neg
  deriving (Eq, Show)

-- Expressions: real-valued
data Exp where
  EStrLit :: String -> Exp
  ERealLit :: Double -> Exp
  EUOp :: UnOp -> Exp -> Exp
  EBin :: BinOp -> Exp -> Exp -> Exp
  EIf :: Exp -> Exp -> Exp -> Exp
  EParens :: Exp -> Exp
  EVar :: String -> Exp
  deriving (Eq, Show)

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
eval env (EBin Times e1 e2) = evalNumeric(*) (eval env e1) (eval env e2)
eval env (EBin Div e1 e2) = evalNumeric (/) (eval env e1) (eval env e2)
eval env (EIf g e1 e2) = case eval env g of
  (Just (VBool True)) -> eval env e1
  (Just (VBool False)) -> eval env e2
  _             -> Nothing
eval env (EParens e) = eval env e
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


evalArithBool :: Num a => (Double -> Double -> Bool) -> Maybe Val -> Maybe Val -> Maybe Val
evalArithBool op x y = case (x, y) of
  (Just (VReal x), Just (VReal y)) -> Just $ VBool $ op x y
  _                  -> Nothing


data Pred = Lit Bool
  | Expr Exp
  | And Pred Pred
  | Or Pred Pred
  | Not Pred
  deriving (Show)

-- Checks that predicate is well formed (ie all terms are booleans)
checkPred :: Env -> Pred -> Bool
checkPred _ (Lit b) = True
checkPred env (Expr e) = case eval env e of
  Just (VBool b) -> True
  _              -> False
checkPred env (And e1 e2) = checkPred env e1 && checkPred env e2
checkPred env (Or e1 e2)  = checkPred env e1 && checkPred env e2
checkPred env (Not e)     = checkPred env e

data Exception = NumArgs Integer [Val]
               | TypeMismatch String Val
               | Parser ParseError
               | BadSpecialForm String Val

type ThrowsError = Either Exception
