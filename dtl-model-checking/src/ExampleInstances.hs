module ExampleInstances
  ( --exporting fromulas --
    fEasy1, fEasy2, fEasy3,
    fMedium1,
    -- exporting automatons
    gnbafEasy1, nbafEasy1, nbafEasy2, nbafMedium1,
    -- exporting transition systems --
    oneAgent1,
    t8States2Agents1, t8States2Agents2,
    t8States2Agents3, t8States2Agents4, t8States2Agents5, t8States2Agents6,
    t8States2Agents7, t8States2Agents8, t8States2Agents9, t8States2Agents10,
    t16States2Agents1, t16States2Agents2,
    t16States2Agents3, t16States2Agents4, t32States2Agents1, t32States2Agents2,
    t64States2Agents1, t64States2Agents2, t128States2Agents1, t128States2Agents2,
    t256States2Agents1, t256States2Agents2, t512States2Agents1, t512States2Agents2,
    t1024States2Agents1, t1024States2Agents2,
    tThesis, tThesisComHolds, tThesisNextNext, tThesisNextNextWitness
    -- end exporting transition systems --
  )

where

-- import           AutomataTheoreticApproach
import CommonTypes
import Utils
import qualified Data.Map.Lazy             as M
import qualified Data.Set                  as S
import qualified DTLFormula                as F
import qualified DTS                       as T
import qualified GNBA                      as G
import qualified NBA                       as N
import System.Random
import qualified BMC                       as B
import qualified AutomataTheoreticApproach as A


-- -----------------------------------------------------------------------------
-- BEGIN: Description of the module
-- -----------------------------------------------------------------------------
-- In this module we generate only variables that are used
-- for testing and debugging
-- -----------------------------------------------------------------------------
-- END: Description of the module
-- -----------------------------------------------------------------------------


-- -----------------------------------------------------------------------------
-- BEGIN: Formulas
-- -----------------------------------------------------------------------------
-- some easy formulas for two agents --
fEasy1 :: F.GlobalFormula
fEasy1 = F.Local 1 (F.Next $ F.PropositionalSymbol "p1")

fEasy2 :: F.GlobalFormula
fEasy2 = F.Local 1 (F.Globally $ F.Implies (F.PropositionalSymbol "p1")(F.PropositionalSymbol "p2"))

fEasy3 :: F.GlobalFormula
fEasy3 = F.Local 1 (F.Comunicates 2 (F.PropositionalSymbol "q_1"))
-- end easy formulas for two agents --

-- some medium difficulty formulas --
fMedium1 :: F.GlobalFormula
fMedium1 = F.Local 1 (F.Implies (F.Comunicates 2 (F.Implies (F.Globally $ F.PropositionalSymbol "q1")
                                                            (F.PropositionalSymbol "q2")))
                                (F.Next $ F.PropositionalSymbol "p1"))
-- end some medium formulas --
-- -----------------------------------------------------------------------------
-- END: Formulas
-- -----------------------------------------------------------------------------

-- -----------------------------------------------------------------------------
-- BEGIN: Some automatons for formulas and the transition systems
-- -----------------------------------------------------------------------------
gnbafEasy1 = A.makeComplementaryGNBA fEasy1 2 [["a", "b"], ["a", "c"]]
nbafEasy1  = A.convertGNBAToNBA gnbafEasy1 (G.getAlphabet gnbafEasy1)

gnbafEasy2 = A.makeComplementaryGNBA fEasy2 2 [["a", "b"], ["a", "c"]]
nbafEasy2  = A.convertGNBAToNBA gnbafEasy2 (G.getAlphabet gnbafEasy2)

gnbafMedium1 = A.makeComplementaryGNBA fMedium1 2 [["a", "b"], ["a", "c"]]
nbafMedium1  = A.convertGNBAToNBA gnbafMedium1 (G.getAlphabet gnbafMedium1)
-- -----------------------------------------------------------------------------
-- END: Some automatons for formulas and the transition systems
-- -----------------------------------------------------------------------------



-- -----------------------------------------------------------------------------
-- BEGIN: Transition Systems
-- -----------------------------------------------------------------------------

-- Simple transition system for just one agent
oneAgent1 :: T.DTS Int Int F.Formula String
oneAgent1 = T.DTS {T.states = S.fromList [1, 2],
                   T.initialStates = S.fromList [1],
                   T.actions = M.fromList [(1, S.fromList ["a"])],
                   T.propSymbols = M.fromList [
                      (1, S.fromList [F.FromLocal $ F.PropositionalSymbol "p"])],
                   T.labelingFunction = M.fromList[
                      ((1, 1), S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
                      ((2, 1), S.fromList [])],
                   T.transitionRelation = M.fromList[
                      ((1, "a"), [2]),
                      ((2, "a"), [1])]}

-- transition systems with 8 states and 2 agents --
t8States2Agents1 :: T.DTS Int Int F.Formula String
t8States2Agents1 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 1)
                                           0.1
                                           0.1

t8States2Agents2 :: T.DTS Int Int F.Formula String
t8States2Agents2 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 2)
                                           0.1
                                           0.1

t8States2Agents3 :: T.DTS Int Int F.Formula String
t8States2Agents3 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 3)
                                           0.1
                                           0.1

t8States2Agents4 :: T.DTS Int Int F.Formula String
t8States2Agents4 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 4)
                                           0.1
                                           0.1

t8States2Agents5 :: T.DTS Int Int F.Formula String
t8States2Agents5 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 5)
                                           0.1
                                           0.1

t8States2Agents6 :: T.DTS Int Int F.Formula String
t8States2Agents6 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 6)
                                           0.1
                                           0.1

t8States2Agents7 :: T.DTS Int Int F.Formula String
t8States2Agents7 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 7)
                                           0.1
                                           0.1

t8States2Agents8 :: T.DTS Int Int F.Formula String
t8States2Agents8 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                          (mkStdGen 8)
                                           0.1
                                           0.1

t8States2Agents9 :: T.DTS Int Int F.Formula String
t8States2Agents9 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 9)
                                           0.1
                                           0.1
t8States2Agents10 :: T.DTS Int Int F.Formula String
t8States2Agents10 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 10)
                                           0.1
                                           0.1
-- end of transition systems with 8 states --

-- transition systems with 16 states and 2 agents --
t16States2Agents1 :: T.DTS Int Int F.Formula String
t16States2Agents1 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 1)
                                           0.1
                                           0.1

t16States2Agents2 :: T.DTS Int Int F.Formula String
t16States2Agents2 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 2)
                                           0.1
                                           0.1

t16States2Agents3 :: T.DTS Int Int F.Formula String
t16States2Agents3 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 3)
                                           0.1
                                           0.1

t16States2Agents4 :: T.DTS Int Int F.Formula String
t16States2Agents4 = T.generateDTSFromStdGen 2
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
t32States2Agents1 :: T.DTS Int Int F.Formula String
t32States2Agents1 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2", F.FromLocal $ F.PropositionalSymbol "p3"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 3)
                                           0.1
                                           0.05

t32States2Agents2 :: T.DTS Int Int F.Formula String
t32States2Agents2 = T.generateDTSFromStdGen 2
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
t64States2Agents1 :: T.DTS Int Int F.Formula String
t64States2Agents1 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2", F.FromLocal $ F.PropositionalSymbol "p3"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2", F.FromLocal $ F.PropositionalSymbol "q3"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 3)
                                           0.1
                                           0.025

t64States2Agents2 :: T.DTS Int Int F.Formula String
t64States2Agents2 = T.generateDTSFromStdGen 2
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
t128States2Agents1 :: T.DTS Int Int F.Formula String
t128States2Agents1 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2", F.FromLocal $ F.PropositionalSymbol "p3", F.FromLocal $ F.PropositionalSymbol "p4"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2", F.FromLocal $ F.PropositionalSymbol "q3"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 3)
                                           0.1
                                           0.0125

t128States2Agents2 :: T.DTS Int Int F.Formula String
t128States2Agents2 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2", F.FromLocal $ F.PropositionalSymbol "p3", F.FromLocal $ F.PropositionalSymbol "p4"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2", F.FromLocal $ F.PropositionalSymbol "q3"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 4)
                                           0.1
                                           0.0125
-- end of transition systems with 128 states --

-- trnasition systems with 128 states --
t256States2Agents1 :: T.DTS Int Int F.Formula String
t256States2Agents1 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2", F.FromLocal $ F.PropositionalSymbol "p3", F.FromLocal $ F.PropositionalSymbol "p4"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2", F.FromLocal $ F.PropositionalSymbol "q3", F.FromLocal $ F.PropositionalSymbol "q4"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 3)
                                           0.1
                                           0.0125

t256States2Agents2 :: T.DTS Int Int F.Formula String
t256States2Agents2 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2", F.FromLocal $ F.PropositionalSymbol "p3", F.FromLocal $ F.PropositionalSymbol "p4"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2", F.FromLocal $ F.PropositionalSymbol "q3", F.FromLocal $ F.PropositionalSymbol "q4"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 4)
                                           0.1
                                           0.0125
-- end of transition systems with 256 states --

-- trnasition systems with 128 states --
t512States2Agents1 :: T.DTS Int Int F.Formula String
t512States2Agents1 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2", F.FromLocal $ F.PropositionalSymbol "p3", F.FromLocal $ F.PropositionalSymbol "p4", F.FromLocal $ F.PropositionalSymbol "p5"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2", F.FromLocal $ F.PropositionalSymbol "q3", F.FromLocal $ F.PropositionalSymbol "q4"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 3)
                                           0.05
                                           0.006

t512States2Agents2 :: T.DTS Int Int F.Formula String
t512States2Agents2 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2", F.FromLocal $ F.PropositionalSymbol "p3", F.FromLocal $ F.PropositionalSymbol "p4", F.FromLocal $ F.PropositionalSymbol "p5"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2", F.FromLocal $ F.PropositionalSymbol "q3", F.FromLocal $ F.PropositionalSymbol "q4"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 4)
                                           0.05
                                           0.006
-- end of transition systems with 512 states --

-- trnasition systems with 128 states --
t1024States2Agents1 :: T.DTS Int Int F.Formula String
t1024States2Agents1 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2", F.FromLocal $ F.PropositionalSymbol "p3", F.FromLocal $ F.PropositionalSymbol "p4", F.FromLocal $ F.PropositionalSymbol "p5"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2", F.FromLocal $ F.PropositionalSymbol "q3", F.FromLocal $ F.PropositionalSymbol "q4", F.FromLocal $ F.PropositionalSymbol "q5"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 3)
                                           0.02
                                           0.003

t1024States2Agents2 :: T.DTS Int Int F.Formula String
t1024States2Agents2 = T.generateDTSFromStdGen 2
                                           [
                                             [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2", F.FromLocal $ F.PropositionalSymbol "p3", F.FromLocal $ F.PropositionalSymbol "p4", F.FromLocal $ F.PropositionalSymbol "p5"],
                                             [F.FromLocal $ F.PropositionalSymbol "q1", F.FromLocal $ F.PropositionalSymbol "q2", F.FromLocal $ F.PropositionalSymbol "q3", F.FromLocal $ F.PropositionalSymbol "q4", F.FromLocal $ F.PropositionalSymbol "q5"]
                                           ]
                                           [["a", "b"], ["a", "c"]]
                                           (mkStdGen 4)
                                           0.02
                                           0.003
-- end of transition systems with 1024 states --


tThesis :: T.DTS Int Int F.Formula String
tThesis = T.DTS {T.states = S.fromList [1, 2, 3, 4],
        T.actions = M.fromList [(1, S.fromList ["a", "b"]), (2, S.fromList ["a", "c"])],
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
tThesisNextNext :: T.DTS Int Int F.Formula String
tThesisNextNext = T.DTS {T.states = S.fromList [1, 2, 3],
        T.actions = M.fromList [(1, S.fromList ["a", "b"]), (2, S.fromList ["a", "c"])],
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
tThesisNextNextWitness :: T.DTS Int Int F.Formula String
tThesisNextNextWitness = T.deleteStates tThesisNextNext [3]


-- A witness for "@_2[X X c_1(p)]"
tThesisComHolds :: T.DTS Int Int F.Formula String
tThesisComHolds = T.DTS {T.states = S.fromList [1, 2],
        T.actions = M.fromList [(1, S.fromList ["a", "b"]), (2, S.fromList ["b"])],
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


-- -----------------------------------------------------------------------------
-- END: Transition Systems
-- -----------------------------------------------------------------------------


