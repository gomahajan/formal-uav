module SMTSolver where

import System.IO
import System.Exit
import System.Process

run :: String -> Double -> IO String
run f delta = do
    let p = (shell ("./dReal/bin/dReal " ++ f ++ " --model --precision " ++ show delta))
            { std_in  = Inherit
            , std_out = CreatePipe
            , std_err = Inherit
            }
    (Nothing, Just out, Nothing, ph) <- createProcess p
    ec <- waitForProcess ph
    hGetContents out


runZ3 :: String -> IO String
run f = do
    let p = (shell ("./z3/bin/z3 " ++ f))
            { std_in  = Inherit
            , std_out = CreatePipe
            , std_err = Inherit
            }
    (Nothing, Just out, Nothing, ph) <- createProcess p
    ec <- waitForProcess ph
    hGetContents out