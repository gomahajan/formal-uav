module SMTSolver where

import System.IO
import System.Exit
import System.Process

run :: String -> String -> Double -> IO String
run args f delta = do
    let p = (shell ("./dReal/bin/dReal " ++ f ++ " --model --precision " ++ show delta ++ " " ++ args))
            { std_in  = Inherit
            , std_out = CreatePipe
            , std_err = Inherit
            }
    (Nothing, Just out, Nothing, ph) <- createProcess p
    ec <- waitForProcess ph
    hGetContents out
