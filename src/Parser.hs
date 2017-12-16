module Parser where

import Control.Monad
import Text.Parsec hiding (crlf)
import Text.Parsec.String
import qualified Text.Parsec.Token as Token
import Text.Parsec.Expr as Expr
import Control.Applicative ((<*))
import Debug.Trace
import Control.Monad.Except
import System.IO
import Numeric
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List

import Logic
import CodeGen

type Assignment = (String, Double)

data Response = Response String [Assignment] deriving (Show)

--Clears whitespace
whitespace = void . many $ oneOf " \t\n"

nonWhitespace = many $ noneOf " \t\n"

-- Various number formats
parseNum = do
  x <- try parseSci <|> try parseDouble <|> parseDInt
  whitespace
  return x

parseDInt :: Parser Double
parseDInt = do
  sign <- many $ char '-'
  x <- many1 digit
  let val = fst . head $ readFloat x
  return $ case sign of
    [] -> val
    _  -> (-1) * val

-- Decimal doubles
parseDouble :: Parser Double
parseDouble = do
  sign <- many $ char '-'
  x <- many1 digit
  char '.'
  y <- many1 digit
  let val = fst . head $ readFloat (x ++ "." ++ y)
  return $ case sign of
    [] -> val
    _  -> (-1) * val

-- Parser for doubles in scientific notation
parseSci :: Parser Double
parseSci = do
  base <- try parseDouble <|> parseDInt
  char 'e'
  ms <- many $ char '-'
  ex <- many1 digit
  let pwr = read ex
  return $ case ms of
    [] -> base * (10 ^ pwr)
    _ -> base / (10 ^ pwr)

--Specification language parsers

opNames :: [String]
opNames = Map.elems unOpTokens ++ Map.elems binOpTokens

opStart :: String
opStart = nub (fmap head opNames)

opLetter :: String
opLetter = nub (concatMap tail opNames)

specLang :: Token.LanguageDef ()
specLang = Token.LanguageDef
  ""
  ""
  "//"
  False
  letter
  alphaNum
  (oneOf Parser.opStart)
  (oneOf Parser.opLetter)
  []
  opNames
  True

lexer :: Token.TokenParser ()
lexer = Token.makeTokenParser specLang

parens = Token.parens lexer

parseDynamics :: Char -> Parser ODE
parseDynamics c = do
  string "d/dt["
  whitespace
  char c
  whitespace
  char ']'
  whitespace
  char '='
  whitespace
  de <- parseODE
  return de
  --return $ EVar "temp"

-- Parse constant definitions
parseDef :: Parser (String, Double)
parseDef = do
  string "#define"
  whitespace
  s <- nonWhitespace
  whitespace
  v <- parseNum
  whitespace
  return (s, v)

parseDomain :: Parser (String, Domain)
parseDomain = do
  string "#domain"
  whitespace
  v <- nonWhitespace
  whitespace
  char '['
  x <- parseNum
  whitespace
  char ','
  whitespace
  y <- parseNum
  whitespace
  char ']'
  whitespace
  return (v, Domain { vmin = x, vmax = y } )

parseODE :: Parser ODE
parseODE = buildExpressionParser (exprTable EUOp EBin) parseLit <?> "ode"

parseLit :: Parser ODE
parseLit = try (parens parseODE) <|> try pNum <|> pStr
  where
    pNum = do
      v <- parseNum
      return $ ERealLit v
    pStr = do
      s <- nonWhitespace
      return $ EStrLit s

-- Expression table
exprTable mkUnary mkBinary = [
  [unary Neg],
  [unary Sin, unary Cos, unary Tan],
  [binary Pow AssocNone],
  [binary Times AssocLeft, binary Div AssocLeft],
  [binary Plus AssocLeft, binary Minus AssocLeft],
  [binary Eq AssocNone, binary Leq AssocNone, binary Lt AssocNone, binary Geq AssocNone, binary Gt AssocNone]]
  where
    unary op = Prefix (Token.reservedOp lexer (unOpTokens Map.! op) >> return (mkUnary op))
    binary op = Infix (Token.reservedOp lexer (binOpTokens Map.! op) >> return (mkBinary op))

-- Tokens
unOpTokens :: Map UnOp String
unOpTokens = Map.fromList [ (Neg, "-")
                      , (Sin, "sin")
                      , (Cos, "cos")
                      , (Tan, "tan")
                      ]

binOpTokens :: Map BinOp String
binOpTokens = Map.fromList [ (Times, "*")
                       , (Plus,      "+")
                       , (Minus,     "-")
                       , (Div,       "/")
                       , (Pow,       "^")
                       , (Eq,        "==")
                       , (Lt,        "<")
                       , (Leq,       "<=")
                       , (Gt,        ">")
                       , (Geq,       ">=")
                       ]
