module AutoBench (benchmarksEasy, benchmarksTwoAgentsEasy,
                  benchmarksTwoAgentsMedium) where

import Criterion (Benchmark, bench, nf)
import           AutomataTheoreticApproach
import qualified Data.Map.Lazy             as M
import qualified Data.Set                  as S
import qualified DTLFormula                as F
import qualified DTS                       as T

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

benchmarksTwoAgentsMedium =
  [
    bench "Testing for alphaBenchmarkMedium1 and tThesis"
          (nf (modelCheck tThesis alphaBenchmarkMedium1) 2)
  ]

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
f1BenchmarkMedium1 = F.Next (F.Globally (F.Implies (F.PropositionalSymbol "p") (F.Comunicates 2 (F.PropositionalSymbol "q"))))
f2BenchmarkMedium1 = F.Implies (F.Next ( F.PropositionalSymbol "q")) (F.Implies (F.Next (F.PropositionalSymbol "q")) (F.PropositionalSymbol "q"))
alphaBenchmarkMedium1 = F.GImplies (F.Local 1 f1BenchmarkMedium1) (F.Local 2 f2BenchmarkMedium1)
