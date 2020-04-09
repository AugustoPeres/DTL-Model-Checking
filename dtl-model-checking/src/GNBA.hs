module GNBA (GNBA(..), empty, addState, addTransition, addFinalSet, addToInitialStates,
            getNeighbours)
where


import qualified          Data.Map.Strict as Map
import Data.List (union)
import Data.Maybe
import CommonTypes

-- This module contains everything needed to work with
-- general non deterministic Buchi automatons
-- s -> represents any type that can represent a state
--      Unlike the module for NBA we do not restrict this to INT
-- a -> represents any type for the alphabet symbol.

data GNBA s a = GNBA { states        :: [s],
                       inicialStates :: [s],
                       finalSets     :: [[s]],
                       delta         :: Map.Map s [(a, s)]
                     }
                     deriving (Show)

instance (Show s, Show a, Ord s) => FiniteGraphRepresentable (GNBA s a) where
  toGraphviz auto =
    "digraph finite_state_machine {\n" ++
    "node[width = 2 height = 2 fontsize = 10];\n" ++
    foldr (\a b -> b ++ foldr (\a' b' -> b' ++ "\"" ++ show a ++ "\"" ++
                                         "->" ++ "\"" ++ show (snd a') ++ "\" " ++
                                         "[label =\" " ++ show (fst a') ++ "\"];\n")
                              ""
                              (getNeighbours auto a))
          ""
          (states auto)
    ++
    "}"


-- -----------------------------------------------------------------------------
-- BEGIN: Getterns for the GNBA
-- -----------------------------------------------------------------------------

-- | Input: Automaton and a state
--   Output: A list with all the neighbours and the respective letter
--           that causes the transition
getNeighbours :: (Ord s) =>
                 GNBA s a ->
                 s ->
                 [(a, s)]
getNeighbours auto s =
  fromMaybe [] ((delta auto) Map.!? s)
-- -----------------------------------------------------------------------------
-- END: Getterns for the GNBA
-- -----------------------------------------------------------------------------




-- -----------------------------------------------------------------------------
-- BEGIN: Functions for adding and deleting stuff from the automaton
-- -----------------------------------------------------------------------------

-- Create an empty automaton
empty :: GNBA s a
empty = GNBA [] [] [] Map.empty


-- | Input: A GNBA and a state
--   Output: A GNBA with that state added to the initial states
addToInitialStates :: (Eq s) => GNBA s a -> s -> GNBA s a
addToInitialStates gnba state=
  GNBA (states gnba `union` [state])
       (inicialStates gnba `union` [state])
       (finalSets gnba)
       (delta gnba)


-- | Input: A GNBA and a state,
--   Output: adds the state to the automaton without any transitions
--   We assume that that state is not in any final set
addState :: (Eq s) =>
            GNBA s a ->
            s ->
            GNBA s a
addState gnba state =
  GNBA (states gnba `union` [state])
       (inicialStates gnba)
       (finalSets gnba)
       (delta gnba)


-- | Input: A GNBA, a state, a letter, a state
--   Output: Adds the transition to that state
addTransition :: (Ord s, Eq a) =>
                 GNBA s a ->
                 s ->
                 a ->
                 s ->
                 GNBA s a
addTransition gnba o a d =
  GNBA (states gnba)
       (inicialStates gnba)
       (finalSets gnba)
       (Map.insert o (newTransition) (delta gnba))
  where newTransition = [(a, d)] `union` (fromMaybe [] (Map.lookup o (delta gnba)))


-- | Input: A GNBA, a list of states,
--   Output: A GNBA with those states added as a final set
--   NOTE: we also add the states to the list of existing states
--         to make sure that no final state is added without being
--         in the states
addFinalSet :: (Ord s) =>
               GNBA s a ->
               [s] ->
               GNBA s a
addFinalSet gnba st =
  GNBA ((states gnba) `union` st)
       (inicialStates gnba)
       ((finalSets gnba) `union` [st])
       (delta gnba)

-- -----------------------------------------------------------------------------
-- END: Functions for adding and deleting stuff from the automaton
-- -----------------------------------------------------------------------------


