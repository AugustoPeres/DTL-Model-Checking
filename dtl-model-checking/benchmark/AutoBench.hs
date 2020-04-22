module AutoBench (benchmarksEasy, benchmarksTwoAgentsEasy,
                  benchmarksTwoAgentsVeryHard, benchmarks8StatesEasyFormulas,
                  benchmarks16StatesEasyFormulas, benchmarks32StatesEasyFormulas,
                  benchmarks64StatesEasyFormulas, benchmarks128StatesEasyFormulas) where

import Criterion (bench, nf)
import           AutomataTheoreticApproach
import qualified Data.Map.Lazy             as M
import qualified Data.Set                  as S
import qualified DTLFormula                as F
import qualified DTS                       as T
import System.Random


oneAgent1 = T.DTS {T.states = S.fromList [1, 2] :: S.Set Int,
                   T.initialStates = S.fromList [1] :: S.Set Int,
                   T.actions = M.fromList [(1::Int, S.fromList ["a"])],
                   T.propSymbols = M.fromList [
                      (1, S.fromList [F.FromLocal $ F.PropositionalSymbol "p"])],
                   T.labelingFunction = M.fromList[
                      ((1, 1), S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
                      ((2, 1), S.fromList [])],
                   T.transitionRelation = M.fromList[
                      ((1, "a"), [2]),
                      ((2, "a"), [1])]}

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
          (nf (modelCheck t8States2Agenst1 fEasy1) 2),
    bench "Testing for transition system t8StatesAgents2 and fEasy1"
          (nf (modelCheck t8States2Agenst2 fEasy1) 2),
    bench "Testing for transition system t8StatesAgents3 and fEasy1"
          (nf (modelCheck t8States2Agenst3 fEasy1) 2),
    bench "Testing for transition system t8StatesAgents4 and fEasy1"
          (nf (modelCheck t8States2Agenst4 fEasy1) 2),
    bench "Testing for transition system t8StatesAgents1 and fEasy2"
          (nf (modelCheck t8States2Agenst1 fEasy2) 2),
    bench "Testing for transition system t8StatesAgents2 and fEasy2"
          (nf (modelCheck t8States2Agenst2 fEasy2) 2),
    bench "Testing for transition system t8StatesAgents3 and fEasy2"
          (nf (modelCheck t8States2Agenst3 fEasy2) 2),
    bench "Testing for transition system t8StatesAgents4 and fEasy2"
          (nf (modelCheck t8States2Agenst4 fEasy2) 2)
 ]

benchmarks16StatesEasyFormulas =
  [
    bench "Testing for transition system t16StatesAgents1 and fEasy1"
          (nf (modelCheck t16States2Agenst1 fEasy1) 2),
    bench "Testing for transition system t16StatesAgents2 and fEasy1"
          (nf (modelCheck t16States2Agenst2 fEasy1) 2),
    bench "Testing for transition system t16StatesAgents3 and fEasy1"
          (nf (modelCheck t16Sates2Agenst3 fEasy1) 2),
    bench "Testing for transition system t16StatesAgents4 and fEasy1"
          (nf (modelCheck t16States2Agenst4 fEasy1) 2),
    bench "Testing for transition system t16StatesAgents1 and fEasy2"
          (nf (modelCheck t16States2Agenst1 fEasy2) 2),
    bench "Testing for transition system t16StatesAgents2 and fEasy2"
          (nf (modelCheck t16States2Agenst2 fEasy2) 2),
    bench "Testing for transition system t16StatesAgents3 and fEasy2"
          (nf (modelCheck t16Sates2Agenst3 fEasy2) 2),
    bench "Testing for transition system t16StatesAgents4 and fEasy2"
          (nf (modelCheck t16States2Agenst4 fEasy2) 2)
 ]

benchmarks32StatesEasyFormulas =
  [
    bench "Testing for transition system t32StatesAgents1 and fEasy1"
          (nf (modelCheck t32Sates2Agenst1 fEasy1) 2),
    bench "Testing for transition system t32StatesAgents2 and fEasy1"
          (nf (modelCheck t32States2Agenst2 fEasy1) 2),
    bench "Testing for transition system t32StatesAgents1 and fEasy2"
          (nf (modelCheck t32Sates2Agenst1 fEasy2) 2),
    bench "Testing for transition system t32StatesAgents2 and fEasy2"
          (nf (modelCheck t32States2Agenst2 fEasy2) 2)
  ]

benchmarks64StatesEasyFormulas =
  [
    bench "Testing for transition system t64StatesAgents1 and fEasy1"
          (nf (modelCheck t64Sates2Agenst1 fEasy1) 2),
    bench "Testing for transition system t64StatesAgents2 and fEasy1"
          (nf (modelCheck t64States2Agenst2 fEasy1) 2),
    bench "Testing for transition system t64StatesAgents1 and fEasy2"
          (nf (modelCheck t64Sates2Agenst1 fEasy2) 2),
    bench "Testing for transition system t64StatesAgents2 and fEasy2"
          (nf (modelCheck t64States2Agenst2 fEasy2) 2)
  ]

benchmarks128StatesEasyFormulas =
  [
    bench "Testing for transition system t128StatesAgents1 and fEasy1"
          (nf (modelCheck t128Sates2Agenst1 fEasy1) 2),
    bench "Testing for transition system t128StatesAgents2 and fEasy1"
          (nf (modelCheck t128States2Agenst2 fEasy1) 2),
    bench "Testing for transition system t128StatesAgents1 and fEasy2"
          (nf (modelCheck t128Sates2Agenst1 fEasy2) 2),
    bench "Testing for transition system t128StatesAgents2 and fEasy2"
          (nf (modelCheck t128States2Agenst2 fEasy2) 2)
  ]

-- This is probably not a good idea
benchmarksTwoAgentsVeryHard =
  [
    bench "Testing for alphaBenchmarkVeryHard1 and tThesis"
          (nf (modelCheck tThesis alphaBenchmarkVeryHard1) 2)
  ]


-- some easy formulas for two agents --
fEasy1 = F.Local 1 (F.Next $ F.PropositionalSymbol "p1") -- can also be used with just one agent
fEasy2 = F.Local 1 (F.Next $ F.Implies (F.Not $ F.PropositionalSymbol "p1")(F.PropositionalSymbol "p2"))
fEasy3 = F.Local 1 (F.Comunicates 2 (F.PropositionalSymbol "q_1"))
-- end easy formulas for two agents --


-- transition systems with 8 states and 2 agents --
t8States2Agenst1 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 1)
                                           0.1
                                           0.1
t8States2Agenst2 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 2)
                                           0.1
                                           0.1
t8States2Agenst3 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 3)
                                           0.1
                                           0.1
t8States2Agenst4 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 4)
                                           0.1
                                           0.1
-- end of transition systems with 8 states --

-- transition systems with 16 states and 2 agents --
t16States2Agenst1 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 1)
                                           0.1
                                           0.1
t16States2Agenst2 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 2)
                                           0.1
                                           0.1
t16Sates2Agenst3 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 3)
                                           0.1
                                           0.1
t16States2Agenst4 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 4)
                                           0.1
                                           0.1
-- end of transition systems with 16 states --

-- trnasition systems with 32 states --
t32Sates2Agenst1 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2", F.FromLocal $ F.PropositionalSymbol "p3"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 3)
                                           0.1
                                           0.05
t32States2Agenst2 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2", F.FromLocal $ F.PropositionalSymbol "p3"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 4)
                                           0.1
                                           0.05
-- end of transition systems with 32 states --

-- trnasition systems with 64 states --
t64Sates2Agenst1 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2", F.FromLocal $ F.PropositionalSymbol "p3"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2", F.FromLocal $ F.PropositionalSymbol "q3"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 3)
                                           0.1
                                           0.025
t64States2Agenst2 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2", F.FromLocal $ F.PropositionalSymbol "p3"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2", F.FromLocal $ F.PropositionalSymbol "q3"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 4)
                                           0.1
                                           0.025
-- end of transition systems with 64 states --

-- trnasition systems with 128 states --
t128Sates2Agenst1 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2", F.FromLocal $ F.PropositionalSymbol "p3", F.FromLocal $ F.PropositionalSymbol "p4"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2", F.FromLocal $ F.PropositionalSymbol "q3"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 3)
                                           0.1
                                           0.0125
t128States2Agenst2 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2", F.FromLocal $ F.PropositionalSymbol "p3", F.FromLocal $ F.PropositionalSymbol "p4"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2", F.FromLocal $ F.PropositionalSymbol "q3"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 4)
                                           0.1
                                           0.0125
-- end of transition systems with 128 states --


tThesis = T.DTS {T.states = S.fromList [1, 2, 3, 4] :: S.Set Int,
        T.actions = M.fromList [(1::Int, S.fromList ["a", "b"]), (2, S.fromList ["a", "c"])],
        T.initialStates = S.fromList [1, 4],
        T.propSymbols = M.fromList [
            (1, S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
            (2, S.fromList [F.FromLocal $ F.PropositionalSymbol "q"])
                    ],
        T.labelingFunction = M.fromList [
                                      ((1, 1), S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
                                      ((1, 2), S.fromList [F.FromLocal $ F.PropositionalSymbol "q"]),
                                      ((2, 1), S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
                                      ((2, 2), S.fromList []),
                                      ((3, 1), S.fromList []),
                                      ((3, 2), S.fromList [F.FromLocal $ F.PropositionalSymbol "q"]),
                                      ((4, 1), S.fromList []),
                                      ((4, 2), S.fromList [])
                                      ],
        T.transitionRelation = M.fromList [
                                          ((1, "a"), [2, 4]),
                                          ((1, "b"), [3]),
                                          ((2, "c"), [1]),
                                          ((3, "b"), [1]),
                                          ((4, "a"), [2])]}


-- A witness for @_1[p] => @_2[X(X p)]. This is achieved by removing the 4th(WORNG!!)
-- state from tThesis and removing p from the second state.
-- NOTE: This still is not enough for the formula to hold. We need to remove the third state
--       otherwise we will just stay in a 1-3-1-3-1-3-1-3 forever without witnessing
--       the satisfaction of XXp
tThesisNextNext = T.DTS {T.states = S.fromList [1, 2, 3] :: S.Set Int,
        T.actions = M.fromList [(1::Int, S.fromList ["a", "b"]), (2, S.fromList ["a", "c"])],
        T.initialStates = S.fromList [1],
        T.propSymbols = M.fromList [
            (1, S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
            (2, S.fromList [F.FromLocal $ F.PropositionalSymbol "q"])
                    ],
        T.labelingFunction = M.fromList [
                                      ((1, 1), S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
                                      ((1, 2), S.fromList [F.FromLocal $ F.PropositionalSymbol "q"]),
                                      ((2, 1), S.fromList []),
                                      ((2, 2), S.fromList []),
                                      ((3, 1), S.fromList []),
                                      ((3, 2), S.fromList [F.FromLocal $ F.PropositionalSymbol "q"])
                                      ],
        T.transitionRelation = M.fromList [
                                          ((1, "a"), [2]),
                                          ((1, "b"), [3]),
                                          ((2, "c"), [1]),
                                          ((3, "b"), [1])]}


-- The final witness for @_1[p] => @_2[XXp]
tThesisNextNextWitness = T.deleteStates tThesisNextNext [3]


-- A witness for "@_2[]c_1(p)"
tThesisComHolds = T.DTS {T.states = S.fromList [1, 2] :: S.Set Int,
        T.actions = M.fromList [(1::Int, S.fromList ["a", "b"]), (2, S.fromList ["b"])],
        T.initialStates = S.fromList [1],
        T.propSymbols = M.fromList [
            (1, S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
            (2, S.fromList [F.FromLocal $ F.PropositionalSymbol "q"])
                    ],
        T.labelingFunction = M.fromList [
                                      ((1, 1), S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
                                      ((1, 2), S.fromList [F.FromLocal $ F.PropositionalSymbol "q"]),
                                      ((2, 1), S.fromList []),
                                      ((2, 2), S.fromList [])
                                      ],
        T.transitionRelation = M.fromList [
                                          ((1, "a"), [2]),
                                          ((2, "b"), [1])]}

-- some formulas used for bechmarking --
f1BenchmarkVeryHard1 = F.Next (F.Globally (F.Implies (F.PropositionalSymbol "p") (F.Comunicates 2 (F.PropositionalSymbol "q"))))
f2BenchmarkVeryHard1 = F.Implies (F.Next ( F.PropositionalSymbol "q")) (F.Implies (F.Next (F.PropositionalSymbol "q")) (F.PropositionalSymbol "q"))
alphaBenchmarkVeryHard1 = F.GImplies (F.Local 1 f1BenchmarkVeryHard1) (F.Local 2 f2BenchmarkVeryHard1)
