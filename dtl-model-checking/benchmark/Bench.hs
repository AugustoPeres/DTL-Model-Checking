import Criterion.Main
import Criterion
import qualified AutoBench
import Criterion.Types
import qualified BMCBench

myConfig :: Config
myConfig = defaultConfig {
              resamples = 3
           }

main :: IO ()
main = defaultMainWith myConfig
  [
    -- bgroup "for one agent easy:" AutoBench.benchmarksEasy,
    -- bgroup "for two agents easy:" AutoBench.benchmarksTwoAgentsEasy,
    bgroup "8 states and easy formulas:" AutoBench.benchmarks8StatesEasyFormulas,
    bgroup "8 states and easy formulas BOUNDED:" BMCBench.benchmarks8StatesEasyFormulas,
    bgroup "16 states and easy formulas:" AutoBench.benchmarks16StatesEasyFormulas,
    bgroup "16 states and easy formulas BOUNDED:" BMCBench.benchmarks16StatesEasyFormulas,
    bgroup "32 states and easy formulas:" AutoBench.benchmarks32StatesEasyFormulas,
    bgroup "32 states and easy formulas BOUNDED:" BMCBench.benchmarks32StatesEasyFormulas,
    bgroup "64 states and easy formulas:" AutoBench.benchmarks64StatesEasyFormulas,
    bgroup "64 states and easy formulas BOUNDED:" BMCBench.benchmarks64StatesEasyFormulas,
    bgroup "128 states and easy formulas:" AutoBench.benchmarks128StatesEasyFormulas,
    bgroup "128 states and easy formulas BOUNDED:" BMCBench.benchmarks128StatesEasyFormulas,
    bgroup "256 states and easy formulas:" AutoBench.benchmarks256StatesEasyFormulas,
    bgroup "256 states and easy formulas: BOUNDED" BMCBench.benchmarks256StatesEasyFormulas,
    bgroup "512 states and easy formulas:" AutoBench.benchmarks512StatesEasyFormulas,
    bgroup "1024 states and easy formulas:" AutoBench.benchmarks1024StatesEasyFormulas,
    bgroup "128 states and medium formulas:" AutoBench.benchmarks512StatesMediumFormulas,
    bgroup "256 states and medium formulas:" AutoBench.benchmarks256StatesMediumFormulas,
    bgroup "512 states and medium formulas:" AutoBench.benchmarks512StatesMediumFormulas,
    bgroup "1024 states and medium formulas:" AutoBench.benchmarks1024StatesMediumFormulas
--    bgroup "Tests for two agents medium:" AutoBench.benchmarksTwoAgentsMedium
  ]
