module AutoBench (benchmarks) where

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

benchmarks =
  [
    bench "Benchmarking @_1 [X p] and transition system oneAgent1"
          (nf (modelCheck oneAgent1 (F.Local 1 (F.Next $ F.PropositionalSymbol "p"))) 1)
  ]
