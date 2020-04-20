import Criterion.Main
import Criterion
import qualified AutoBench

main :: IO ()
main = defaultMain
  [
    bgroup "Tests for one agent easy:" AutoBench.benchmarksEasy,
    bgroup "Tests for two agents easy:" AutoBench.benchmarksTwoAgentsEasy,
    bgroup "Tests for two agents medium:" AutoBench.benchmarksTwoAgentsMedium
  ]
