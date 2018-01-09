module Utils where

-- Logging utilities
genCSV :: (Show a) => [a] -> String
genCSV []     = "\n"
genCSV (x:xs) = (genCSV' (show x) xs) ++ "\n"

genCSV' :: (Show a) => String -> [a] -> String
genCSV' s []     = s
genCSV' s [x]    = s ++ "," ++ show x
genCSV' s (x:xs) = genCSV' (s ++ "," ++ show x) xs
