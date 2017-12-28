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

parseFromFile :: Parser a -> String -> IO (Either ParseError a)
parseFromFile parser fname = do
  input <- readFile fname
  return $ parse parser fname input

--Clears whitespace
whitespace = void . many $ oneOf " \t\n"

ignore = do
  whitespace
  skipMany comment
  whitespace

name = many1 $ noneOf " \t\n:#"

comment :: Parser String
comment = do
  string "//"
  s <- manyTill anyChar newline
  return s

-- Various number formats
parseNum = do
  x <- try parseSci <|> try parseDouble <|> parseDInt
  ignore
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

-- Rationals
parseRational :: Parser Double
parseRational = do
  string "(/"
  whitespace
  num <- parseDouble
  whitespace
  den <- parseDouble
  whitespace
  string ")"
  return $ num/den

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

parseInt = read <$> many1 digit

-- Specification language parsers

-- Parses complete specification
parseDecls :: Parser Decls
parseDecls = do
  ignore
  defs <- many $ try parseDef
  ignore
  doms <- many $ try parseDomain
  ignore
  string "#complete_dynamics" -- relational dynamics
  ignore
  modes <- many1 $ try parseMode
  ignore
  string "#uav" -- uav dynamics
  ignore
  uavms <- many1 $ try parseUAV
  ignore
  s <- many1 $ try parseSensor
  ignore
  return Decls {
    _defns = Map.fromList defs,
    _varDomains = Map.fromList doms,
    _modeDefs = modes,
    _uavModes = uavms,
    _sensors = s
  }

opNames :: [String]
opNames = Map.elems unOpTokens ++ Map.elems binOpTokens ++ ["//"]

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
  s <- name
  whitespace
  v <- parseNum
  ignore
  --whitespace
  return (s, v)

parseDomain :: Parser (String, Domain)
parseDomain = do
  string "#domain"
  whitespace
  v <- name
  whitespace
  char '['
  x <- parseNum
  whitespace
  char ','
  whitespace
  y <- parseNum
  whitespace
  char ']'
  ignore
  return (v, Domain { vmin = Just x, vmax = Just y } )

parseMode :: Parser Mode
parseMode = do
  ignore
  string "mode"
  whitespace
  x <- parseInt
  whitespace
  char ':'
  ignore
  string "uav"
  whitespace
  char ':'
  whitespace
  uavm <- name
  ignore
  string "sensor"
  whitespace
  char ':'
  whitespace
  sm <- name
  ignore
  return Mode { modeId = x, uavMode = uavm, sensorMode = sm }

parseDynamic :: String -> Parser ODE
parseDynamic v = do
  string $ "d/dt[" ++ v ++ "]"
  whitespace
  char '='
  whitespace
  diff <- parseODE
  return diff

parseUAV :: Parser UAVMode
parseUAV = do
  n <- name
  whitespace
  char ':'
  ignore
  dx <- parseDynamic "x"
  ignore
  db <- parseDynamic "b"
  ignore
  return UAVMode { modeName = n, xde = dx, bde = db }


parseSensor :: Parser Sensor
parseSensor = do
  ignore
  string "#sensor"
  whitespace
  i <- parseInt
  ignore
  char 'x'
  whitespace
  char '='
  whitespace
  x <- parseNum
  ignore
  ms <- many1 (try parseSMode)
  return Sensor { sId = i, position = x, modes = Map.fromList ms }

parseSMode :: Parser (String, ODE)
parseSMode = do
  n <- name
  whitespace
  char ':'
  ignore
  string "d/dt[q]"
  whitespace
  char '='
  whitespace
  form <- parseODE
  return (n, form)

parseODE :: Parser ODE
parseODE = buildExpressionParser (exprTable EUOp EBin) parseLit <?> "ode"

parseLit :: Parser ODE
parseLit = try (parens parseODE) <|> try pNum <|> pStr
  where
    pNum = do
      v <- parseNum
      return $ ERealLit v
    pStr = do
      s <- name
      whitespace
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
