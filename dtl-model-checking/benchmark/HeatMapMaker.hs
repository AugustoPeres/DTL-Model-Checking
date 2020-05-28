import           AutomataTheoreticApproach as A
import           BMC                       as B
import           CommonTypes
import           DTLFormula                as F
import           DTS                       as T
import ExampleInstances

import System.TimeIt
import Control.Monad.IO.Class

formulasWithLength2 :: [F.GlobalFormula]
formulasWithLength2 =
  map read [
  "@_1((p1)=>(p2))",
  "@_1(c_2(q1))",
  "@_1(X(p1))",
  "@_1(G(p1))"
           ]

formulasWithLength3 :: [F.GlobalFormula]
formulasWithLength3 =
  map read [
  "@_1((X(p1))=>(p2))",
  "@_1((c_2(q1))=>(p1))",
  "@_1((c_2(G(q1))))",
  "(@_1(p1))=>(@_2(q1))"
           ]

formulasWithLength4 :: [F.GlobalFormula]
formulasWithLength4 =
  map read [
  "@_1((c_2(q1))=>(~(p1)))",
  "@_1((c_2(q1))=>(X(p1)))",
  "(@_1(p1))=>(@_2(~(q1)))",
  "@_1(c_2(~(G(q1))))"
           ]

trs :: [(T.DTS Int Int F.Formula String, Int)]
trs =
  [ -- systems with 8 states
    (t8States2Agents1, 8),
    (t8States2Agents2, 8),
    (t8States2Agents3, 8),
    (t8States2Agents4, 8)
  ]

size2 :: [(F.GlobalFormula, (T.DTS Int Int F.Formula String, Int))]
size2 = [(f, t) | f <- formulasWithLength2, t <- trs]

timeItPureNamed :: Control.Monad.IO.Class.MonadIO m => (Int -> t) -> Int -> String -> m Int
timeItPureNamed f v name = timeItNamed name $ f v `seq` return v


main :: IO ()
main = do
  let timesSize2 = map (\x -> timeItPureNamed (A.modelCheck (fst $ snd x) (fst x)) 2 ("l 2" ++ show (snd $ snd x))) size2
  print timesSize2
  -- s <- timeItPureNamed (A.modelCheck t8States2Agents1 (formulasWithLength2!!1)) 2 "l 2"
  -- putStrLn $ show s
