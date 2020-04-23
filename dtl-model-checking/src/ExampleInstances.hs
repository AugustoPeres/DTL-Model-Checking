module ExampleInstances
  ( -- exporting transition systems --
    oneAgent1, fEasy1, fEasy2, fEasy3, t8States2Agents1, t8States2Agents2,
    t8States2Agents3, t8States2Agents4, t16States2Agents1, t16States2Agents2,
    t16States2Agents3, t16States2Agents4, t32States2Agents1, t32States2Agents2,
    t64States2Agents1, t64States2Agents2, t128States2Agents1, t128States2Agents2,
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
import System.Random


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
fEasy2 = F.Local 1 (F.Next $ F.Implies (F.Not $ F.PropositionalSymbol "p1")(F.PropositionalSymbol "p2"))

fEasy3 :: F.GlobalFormula
fEasy3 = F.Local 1 (F.Comunicates 2 (F.PropositionalSymbol "q_1"))
-- end easy formulas for two agents --


-- -----------------------------------------------------------------------------
-- END: Formulas
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

