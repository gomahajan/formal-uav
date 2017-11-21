module Dreach where
import System.IO
import System.Exit
import System.Process

run :: IO String
run = do
    let p = (shell "./dReal/bin/dReach -k 0 uav.drh --visualize --precision=0.1")
            { std_in  = Inherit
            , std_out = CreatePipe
            , std_err = Inherit
            }
    (Nothing, Just out, Nothing, ph) <- createProcess p
    ec <- waitForProcess ph
    hGetContents out
