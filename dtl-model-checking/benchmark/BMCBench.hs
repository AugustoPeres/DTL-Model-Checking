module BMCBench (benchmarks8StatesEasyFormulas, benchmarks16StatesEasyFormulas,
                benchmarks32StatesEasyFormulas, benchmarks64StatesEasyFormulas,
                benchmarks128StatesEasyFormulas, benchmarks256StatesEasyFormulas)
  where


import Criterion (bench, nf)
import BMC
--import qualified Data.Map.Lazy             as M
--import qualified Data.Set                  as S
import qualified DTLFormula                as F
--import qualified DTS                       as T
--import System.Random
import ExampleInstances

benchmarks8StatesEasyFormulas =
  [
    bench "Testing for transition system t8StatesAgents1 and fEasy1 BOUNDED"
          (nf (modelCheckWCE t8States2Agents1 fEasy1 2 0) 10),
    bench "Testing for transition system t8StatesAgents2 and fEasy1 BOUNDED"
          (nf (modelCheckWCE t8States2Agents2 fEasy1 2 0) 10),
    bench "Testing for transition system t8StatesAgents3 and fEasy1 BOUNDED"
          (nf (modelCheckWCE t8States2Agents3 fEasy1 2 0) 10),
    bench "Testing for transition system t8StatesAgents4 and fEasy1 BOUNDED"
          (nf (modelCheckWCE t8States2Agents4 fEasy1 2 0) 10) ]

benchmarks16StatesEasyFormulas =
  [
    bench "Testing for transition system t16StatesAgents1 and fEasy1 BOUNDED"
          (nf (modelCheckWCE t16States2Agents1 fEasy1 2 0) 10),
    bench "Testing for transition system t16StatesAgents2 and fEasy1 BOUNDED"
          (nf (modelCheckWCE t16States2Agents2 fEasy1 2 0) 10),
    bench "Testing for transition system t16StatesAgents3 and fEasy1 BOUNDED"
          (nf (modelCheckWCE t16States2Agents3 fEasy1 2 0) 10),
    bench "Testing for transition system t16StatesAgents4 and fEasy1 BOUNDED"
          (nf (modelCheckWCE t16States2Agents4 fEasy1 2 0) 10) ]

benchmarks32StatesEasyFormulas =
  [
    bench "Testing for transition system t32StatesAgents1 and fEasy1 BOUNDED"
          (nf (modelCheckWCE t32States2Agents1 fEasy1 2 0) 10),
    bench "Testing for transition system t32StatesAgents2 and fEasy1 BOUNDED"
          (nf (modelCheckWCE t32States2Agents2 fEasy1 2 0) 10),
    bench "Testing for transition system t32StatesAgents1 and fEasy2 BOUNDED"
          (nf (modelCheckWCE t32States2Agents1 fEasy2 2 0) 10),
    bench "Testing for transition system t32StatesAgents2 and fEasy2 BOUNDED"
          (nf (modelCheckWCE t32States2Agents1 fEasy2 2 0) 10) ]

benchmarks64StatesEasyFormulas =
  [
    bench "Testing for transition system t64StatesAgents1 and fEasy1 BOUNDED"
          (nf (modelCheckWCE t64States2Agents1 fEasy1 2 0) 10),
    bench "Testing for transition system t64StatesAgents2 and fEasy1 BOUNDED"
          (nf (modelCheckWCE t64States2Agents2 fEasy1 2 0) 10),
    bench "Testing for transition system t64StatesAgents1 and fEasy2 BOUNDED"
          (nf (modelCheckWCE t64States2Agents1 fEasy2 2 0) 10),
    bench "Testing for transition system t64StatesAgents2 and fEasy2 BOUNDED"
          (nf (modelCheckWCE t64States2Agents1 fEasy2 2 0) 10) ]

benchmarks128StatesEasyFormulas =
  [
    bench "Testing for transition system t128StatesAgents1 and fEasy1 BOUNDED"
          (nf (modelCheckWCE t128States2Agents1 fEasy1 2 0) 10),
    bench "Testing for transition system t128StatesAgents2 and fEasy1 BOUNDED"
          (nf (modelCheckWCE t128States2Agents2 fEasy1 2 0) 10),
    bench "Testing for transition system t128StatesAgents1 and fEasy2 BOUNDED"
          (nf (modelCheckWCE t128States2Agents1 fEasy2 2 0) 10),
    bench "Testing for transition system t128StatesAgents2 and fEasy2 BOUNDED"
          (nf (modelCheckWCE t128States2Agents1 fEasy2 2 0) 10) ]

benchmarks256StatesEasyFormulas =
  [
    bench "Testing for transition system t256StatesAgents1 and fEasy1 BOUNDED"
          (nf (modelCheckWCE t256States2Agents1 fEasy1 2 0) 10),
    bench "Testing for transition system t256StatesAgents2 and fEasy1 BOUNDED"
          (nf (modelCheckWCE t256States2Agents2 fEasy1 2 0) 10),
    bench "Testing for transition system t256StatesAgents1 and fEasy2 BOUNDED"
          (nf (modelCheckWCE t256States2Agents1 fEasy2 2 0) 10),
    bench "Testing for transition system t256StatesAgents2 and fEasy2 BOUNDED"
          (nf (modelCheckWCE t256States2Agents1 fEasy2 2 0) 10) ]
