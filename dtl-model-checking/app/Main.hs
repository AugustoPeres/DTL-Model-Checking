{-# OPTIONS_GHC -fforce-recomp    #-}
{-# OPTIONS_GHC -O2               #-}
module Main where

import           System.Environment
import           System.Exit

import           AutomataTheoreticApproach as A
import           BMC                       as B
import           CommonTypes
import           DTLFormula                as F
import           DTS                       as T

--import Lib

usage = putStrLn "Usage: -modelCheck <filename> <formula> <number of agents>\n.\n.\n."

exit = exitWith ExitSuccess

parse arguments
  | arguments == []     = usage >> exit
  | arguments == ["-h"] = usage >> exit
  | head arguments == "-toGraphviz" =
    do tr' <- tr
       putStrLn $ toGraphviz tr' ++
                  "========== Actual verified Transition system ==========\n" ++
                  toGraphviz (T.fullSimplify tr')
  | head arguments == "-modelCheck" =
    if "-bounded" `elem` arguments
    then
      do tr' <- tr
         putStrLn (show $ B.modelCheckUntilK tr' formula nagents 0 maxbound)
    else
      do tr' <- tr
         putStrLn (show $ A.modelCheck tr' formula nagents)
  | head arguments == "-oneCounterExample" =
    if "-bounded" `elem` arguments
    then
       do tr' <- tr
          putStrLn (show $ B.modelCheckWCE tr' formula nagents 0 maxbound)
    else
       do tr' <- tr
          putStrLn (show $ A.modelCheckOneCounterExample tr' formula nagents)
  where tr       = dtsFromFile (arguments!!1)
        formula  = read (arguments!!2) :: F.GlobalFormula
        nagents  = read (arguments!!3) :: Int
        maxbound = read (arguments!!5) :: Int


dtsFromFile :: String -> IO (T.DTS Int Int F.Formula String)
dtsFromFile fileName =
  do f <- readFile fileName
     return (T.parseFromString f)

main :: IO ()
main = getArgs >>= parse

