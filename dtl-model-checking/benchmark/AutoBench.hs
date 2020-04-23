module AutoBench (benchmarksEasy, benchmarksTwoAgentsEasy , benchmarks8StatesEasyFormulas,
                  benchmarks16StatesEasyFormulas, benchmarks32StatesEasyFormulas,
                  benchmarks64StatesEasyFormulas, benchmarks128StatesEasyFormulas) where

import Criterion (bench, nf)
import           AutomataTheoreticApproach
--import qualified Data.Map.Lazy             as M
--import qualified Data.Set                  as S
import qualified DTLFormula                as F
--import qualified DTS                       as T
--import System.Random
import ExampleInstances


benchmarksEasy =
  [
    bench "Benchmarking @_1 [X p] and transition system oneAgent1"
          (nf (modelCheck oneAgent1 (F.Local 1 (F.Next $ F.PropositionalSymbol "p"))) 1),
    bench "Benchamarking @_1 [X p => ~p] and transtion system oneAgent"
          (nf (modelCheck oneAgent1 (F.Local 1 (F.Implies (F.PropositionalSymbol "p") (F.Not $ F.PropositionalSymbol "p")))) 1)
  ]



benchmarksTwoAgentsEasy =
  [
    bench "Testing for @_1[X p], and the DTS in the thesis part of SAT"
          (nf (modelCheck tThesis (F.Local 1 (F.Next $ F.PropositionalSymbol "p"))) 2),
    bench "Testing for @_1[c_2[~q]], and the transition system tThesis"
          (nf (modelCheck tThesis (F.Local 1 (F.Comunicates 2 (F.Not $ F.PropositionalSymbol "q"))) ) 2),
    bench "Testing for @_1[p] => @_2[F q] and for transition system in thesis"
          (nf (modelCheck tThesis (F.GImplies (F.Local 1 (F.PropositionalSymbol "p")) (F.Local 2 (F.Not(F.Globally(F.Not $ F.PropositionalSymbol "q")))))) 2),
    bench "Testing for @_1[p] => @_2[X(X q)] and for transition system tThesis"
          (nf (modelCheck tThesis (F.GImplies (F.Local 1 (F.PropositionalSymbol "p")) (F.Local 2 (F.Next (F.Next $ F.PropositionalSymbol "q"))))) 2)
  ]

benchmarks8StatesEasyFormulas =
  [
    bench "Testing for transition system t8StatesAgents1 and fEasy1"
          (nf (modelCheck t8States2Agents1 fEasy1) 2),
    bench "Testing for transition system t8StatesAgents2 and fEasy1"
          (nf (modelCheck t8States2Agents2 fEasy1) 2),
    bench "Testing for transition system t8StatesAgents3 and fEasy1"
          (nf (modelCheck t8States2Agents3 fEasy1) 2),
    bench "Testing for transition system t8StatesAgents4 and fEasy1"
          (nf (modelCheck t8States2Agents4 fEasy1) 2),
    bench "Testing for transition system t8StatesAgents1 and fEasy2"
          (nf (modelCheck t8States2Agents1 fEasy2) 2),
    bench "Testing for transition system t8StatesAgents2 and fEasy2"
          (nf (modelCheck t8States2Agents2 fEasy2) 2),
    bench "Testing for transition system t8StatesAgents3 and fEasy2"
          (nf (modelCheck t8States2Agents3 fEasy2) 2),
    bench "Testing for transition system t8StatesAgents4 and fEasy2"
          (nf (modelCheck t8States2Agents4 fEasy2) 2)
 ]

benchmarks16StatesEasyFormulas =
  [
    bench "Testing for transition system t16StatesAgents1 and fEasy1"
          (nf (modelCheck t16States2Agents1 fEasy1) 2),
    bench "Testing for transition system t16StatesAgents2 and fEasy1"
          (nf (modelCheck t16States2Agents2 fEasy1) 2),
    bench "Testing for transition system t16StatesAgents3 and fEasy1"
          (nf (modelCheck t16States2Agents3 fEasy1) 2),
    bench "Testing for transition system t16StatesAgents4 and fEasy1"
          (nf (modelCheck t16States2Agents4 fEasy1) 2),
    bench "Testing for transition system t16StatesAgents1 and fEasy2"
          (nf (modelCheck t16States2Agents1 fEasy2) 2),
    bench "Testing for transition system t16StatesAgents2 and fEasy2"
          (nf (modelCheck t16States2Agents2 fEasy2) 2),
    bench "Testing for transition system t16StatesAgents3 and fEasy2"
          (nf (modelCheck t16States2Agents3 fEasy2) 2),
    bench "Testing for transition system t16StatesAgents4 and fEasy2"
          (nf (modelCheck t16States2Agents4 fEasy2) 2)
 ]

benchmarks32StatesEasyFormulas =
  [
    bench "Testing for transition system t32StatesAgents1 and fEasy1"
          (nf (modelCheck t32States2Agents1 fEasy1) 2),
    bench "Testing for transition system t32StatesAgents2 and fEasy1"
          (nf (modelCheck t32States2Agents2 fEasy1) 2),
    bench "Testing for transition system t32StatesAgents1 and fEasy2"
          (nf (modelCheck t32States2Agents1 fEasy2) 2),
    bench "Testing for transition system t32StatesAgents2 and fEasy2"
          (nf (modelCheck t32States2Agents2 fEasy2) 2)
  ]

benchmarks64StatesEasyFormulas =
  [
    bench "Testing for transition system t64StatesAgents1 and fEasy1"
          (nf (modelCheck t64States2Agents1 fEasy1) 2),
    bench "Testing for transition system t64StatesAgents2 and fEasy1"
          (nf (modelCheck t64States2Agents2 fEasy1) 2),
    bench "Testing for transition system t64StatesAgents1 and fEasy2"
          (nf (modelCheck t64States2Agents1 fEasy2) 2),
    bench "Testing for transition system t64StatesAgents2 and fEasy2"
          (nf (modelCheck t64States2Agents2 fEasy2) 2)
  ]

benchmarks128StatesEasyFormulas =
  [
    bench "Testing for transition system t128StatesAgents1 and fEasy1"
          (nf (modelCheck t128States2Agents1 fEasy1) 2),
    bench "Testing for transition system t128StatesAgents2 and fEasy1"
          (nf (modelCheck t128States2Agents2 fEasy1) 2),
    bench "Testing for transition system t128StatesAgents1 and fEasy2"
          (nf (modelCheck t128States2Agents1 fEasy2) 2),
    bench "Testing for transition system t128StatesAgents2 and fEasy2"
          (nf (modelCheck t128States2Agents2 fEasy2) 2)
  ]

-- This is probably not a good idea
-- benchmarksTwoAgentsVeryHard =
--   [
--     bench "Testing for alphaBenchmarkVeryHard1 and tThesis"
--           (nf (modelCheck tThesis alphaBenchmarkVeryHard1) 2)
--   ]

-- some formulas used for bechmarking --
-- f1BenchmarkVeryHard1 = F.Next (F.Globally (F.Implies (F.PropositionalSymbol "p") (F.Comunicates 2 (F.PropositionalSymbol "q"))))
-- f2BenchmarkVeryHard1 = F.Implies (F.Next ( F.PropositionalSymbol "q")) (F.Implies (F.Next (F.PropositionalSymbol "q")) (F.PropositionalSymbol "q"))
-- alphaBenchmarkVeryHard1 = F.GImplies (F.Local 1 f1BenchmarkVeryHard1) (F.Local 2 f2BenchmarkVeryHard1)
