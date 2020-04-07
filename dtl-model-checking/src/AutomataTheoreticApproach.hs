module AutomataTheoreticApproach (modelCheck)
  where


import           CommonTypes
import           Data.List     (union)
import qualified Data.Map.Lazy as M
import qualified Data.Set      as S
import qualified DTLFormula    as F
import qualified DTS           as T
import qualified GNBA          as G
import qualified NBA           as N

-- import missing that has the GNBA module

-- -----------------------------------------------------------------------------
-- BEGIN: Description of the module
-- -----------------------------------------------------------------------------

-- This module contains the automata theoretic approach to model checking.
-- It is here that we build the complementary automaton for a given DTL formula.

-- STEPS: In model checking:
--        1. Build the complementary automaton
--        2. Make the product with the transition function
--        3. Use kosaraju to find the strongly connected components

-- -----------------------------------------------------------------------------
-- END: Description of the module
-- -----------------------------------------------------------------------------

-- | Input: A transition system, a DTL formula and an integer.
--   Output: Yes iff the transition system satisfies the formula
--   This is the MAIN function on the module.
modelCheck :: (Ord s, Ord i, Ord prop, Ord a) =>
              T.DTS s i prop a ->
              F.Formula ->
              Int -> -- number of agents
              Bool
modelCheck t alpha n = undefined


-- -----------------------------------------------------------------------------
-- BEGIN: Making the automaton for the complementary language
-- -----------------------------------------------------------------------------

makeComplementaryGNBA :: F.Formula ->
                         Int ->          -- number of agents
                         [[a]] ->        -- list with the actions
                         [S.Set prop] -> -- propositional symbols for each agent
                         G.GNBA (S.Set F.Formula) (S.Set prop, a)
makeComplementaryGNBA = undefined
-- -----------------------------------------------------------------------------
-- END: Making the automaton for the complementary language
-- -----------------------------------------------------------------------------




-- | Input: A DTS and an automaton
--   Output: The product as defined in my thesis
--   NOTE: The returned transition has a different labeling function.
--         This new transition system uses the state of the automaton
--         in the label of the local states.
--   NOTE: The states also change because they are the dot product.
dotProduct :: (Ord s , Ord i, Ord prop, Ord a) =>
              T.DTS s i prop a ->
              N.NBA (S.Set prop, a) ->
              T.DTS (s, N.State) i N.State a
dotProduct dts auto =
  -- adding actions --
  --dtsWithInitialStates
  dtsWithTransitions
  where newStates = [(s, q) | s <- statesT, q <- statesN]
        statesN = N.states auto
        statesT = S.toList $ T.states dts
        agents = T.getAgents dts
        t1 = T.createFromStates newStates
        -- adding actions --
        dtsWithactions = foldr (\x y -> T.addActionAgent y (snd x) (fst x))
                               t1
                               (concatMap (\x -> zip (cycle [x]) (T.getActionsAgent dts x)) agents)
        -- adding initial states --
        allActions = T.getAllActions dts
        initialStatesT = S.toList $ T.initialStates dts
        initialStatesN = N.inicialStates auto
        dtsWithInitialStates = foldr (\x y -> T.addToInitialStates y x)
                                     dtsWithactions
                                     [(s, q) |s <- initialStatesT, q <- statesN,
                                              any
                                              (\x -> q `elem`
                                                   (foldr (\y z -> N.getNeighboursGeneral
                                                                   auto
                                                                   [x]
                                                                   (S.fromList $ T.getLabel dts s, y)
                                                                   `union` z)
                                                          []
                                                          allActions
                                                    )
                                                )
                                                initialStatesN]
        -- adding the propositional symbols --
        dtsWithLabels = foldr (\x y -> foldr (\ag y' -> T.addStateLabel y' x ag [snd x])
                                             y
                                             agents)
                              dtsWithactions
                              newStates
        -- adding to the transition relation --
        dtsWithTransitions = foldr (\x y -> T.addTransitionSafe y (fst $ fst x) (snd $ fst x) (snd x) )
                                   dtsWithLabels
                                   [((s, s'), a) | s <- newStates,
                                                   s' <- newStates,
                                                   a <- allActions,
                                                   transitionIsPossible s s' a]
        transitionIsPossible s s' a = ((snd s')
                                       `elem`
                                       (N.getNeighboursGeneral auto
                                                               [(snd s)]
                                                               (S.fromList $ T.getLabel dts (fst s'), a)))
                                      &&
                                      (T.isTransitionOfSystem dts (fst s) (fst s') a)

-- just some test instances --
t = T.DTS {T.states = S.fromList [1, 2, 3, 4],
         T.actions = M.fromList [(1, S.fromList ["a", "b"]), (2, S.fromList ["a", "c"])],
         T.initialStates = S.fromList [1, 4],
        T.propSymbols = M.fromList [
            (1, S.fromList ["p1", "q1"]),
            (2, S.fromList ["p2", "q2'"])
                    ],
        T.labelingFunction = M.fromList [
                                      ((1, 1), S.fromList ["p"]),
                                      ((1, 2), S.fromList ["q"]),
                                      ((2, 1), S.fromList ["p"]),
                                      ((2, 2), S.fromList []),
                                      ((3, 1), S.fromList []),
                                      ((3, 2), S.fromList ["q"]),
                                      ((4, 1), S.fromList []),
                                      ((4, 2), S.fromList [])
                                      ],
        T.transitionRelation = M.fromList [((3, "a"), 4), ((4, "a"), 1)]}

g = N.NBA { N.states = [1, 2, 3],
            N.finalStates = [1],
            N.inicialStates = [1, 2],
            N.delta = M.fromList [(1, [((S.fromList ["p"],"a"), 1), ((S.fromList ["q"],"b"), 2), ((S.fromList ["p"], "a"), 3)]) , (2, [((S.fromList ["p", "q"], "c"),3), ((S.fromList ["p", "q"],"a"), 1), ((S.fromList [],"a"), 3)]), (3, [(((S.fromList ["p", "q"],"c")), 3)])]
        }
