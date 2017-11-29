module SMTSolver where
import System.IO
import System.Exit
import System.Process

run :: IO String
run = do
    let p = (shell "./dReal/bin/dReal uav_dreal_complete.smt2 --model")
            { std_in  = Inherit
            , std_out = CreatePipe
            , std_err = Inherit
            }
    (Nothing, Just out, Nothing, ph) <- createProcess p
    ec <- waitForProcess ph
    hGetContents out
