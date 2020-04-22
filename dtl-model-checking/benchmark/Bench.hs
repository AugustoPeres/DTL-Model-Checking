import Criterion.Main
import Criterion
import qualified AutoBench

main :: IO ()
main = defaultMain
  [
    bgroup "for one agent easy:" AutoBench.benchmarksEasy,
    bgroup "for two agents easy:" AutoBench.benchmarksTwoAgentsEasy,
    bgroup "8 states and easy formulas:" AutoBench.benchmarks8StatesEasyFormulas,
    bgroup "16 states and easy formulas:" AutoBench.benchmarks16StatesEasyFormulas,
    bgroup "32 states and easy formulas:" AutoBench.benchmarks32StatesEasyFormulas,
    bgroup "64 states and easy formulas:" AutoBench.benchmarks64StatesEasyFormulas,
    bgroup "128 states and easy formulas:" AutoBench.benchmarks128StatesEasyFormulas
--    bgroup "Tests for two agents medium:" AutoBench.benchmarksTwoAgentsMedium
  ]
