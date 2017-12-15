module SMTSolver where


import System.IO
import System.Exit
import System.Process

data SolverConfig = SolverConfig {
  solverArgs :: String,
  dRealVersion :: Int,
  dRealPath :: String
} deriving (Show, Eq)

run :: SolverConfig -> String -> Double -> IO String
run sconf f delta = do
    let p = (shell (dRealPath sconf ++ " " ++ f ++ " --model --precision " ++ show delta ++ " " ++ solverArgs sconf))
            { std_in  = Inherit
            , std_out = CreatePipe
            , std_err = Inherit
            }
    (Nothing, Just out, Nothing, ph) <- createProcess p
    ec <- waitForProcess ph
    hGetContents out
