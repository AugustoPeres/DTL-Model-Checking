module DTS (DTS, )
where

import           CommonTypes
import qualified Data.Map.Lazy as M
import           Data.Maybe
import qualified Data.Set      as S
-- -----------------------------------------------------------------------------
-- BEGIN: Definition of destributed transition system
-- -----------------------------------------------------------------------------

-- This is the representation of transition systems as algebraic data types
-- s -> Denotes the type of the variables that will consist of the sets
-- i -> Denotes the type variable that will be used to represent agent id
-- a -> Denotes the type variable that will be used to represent actions
-- prop -> Denotes the type variable that will be used to represent the propositional
--         symbols
-- states is just a set of states
-- actions is a mapping from the agents to the actions that are available to them
-- initialStates is a Set of initial sets
-- propSymbols is a mapping from agents to the propositional symbols available to each agent
-- labelingFunction is a mapping from states to a list of sets. Corresponding to each
--                  local labeling function
-- transitionRelation is a mapping from a state and an action to a different state.
--                    NOTE: this definition is assuming a deterministic approach to
--                          transition systems
data DTS s i prop a = DTS {
                          states             :: S.Set s,
                          actions            :: M.Map i (S.Set a),
                          initialStates      :: S.Set s,
                          propSymbols        :: M.Map i (S.Set prop),
                          labelingFunction   :: M.Map s [S.Set prop],
                          transitionRelation :: M.Map (s, a) s
                          } deriving (Show)
-- -----------------------------------------------------------------------------
-- END: Definition of destributed transition system
-- -----------------------------------------------------------------------------

instance (Show s, Show prop, Show a, Ord s) => FiniteGraphRepresentable (DTS s i prop a) where
  toGraphviz system =
    "Digraph {\n" ++
    foldr (\a b -> b ++ show a ++ " [label =" ++ (show $ getter a) ++ ",shape=box]") "" sts ++
    "}"
    where sts = states system
          l = labelingFunction system
          getter s = fromJust $ (M.lookup s l)


-- | Input: Receives a distributed transiotion system a state, a list of lists
--          of propositional symbosl and a boolean
--   Output: A transition system with the state added, the state with
--           is labeled by the given list
--           If true is give to the function we add that state to the list of all
--           initial States.
--   NOTE: we do not check if this is safe in any way
--   NOTE: Because we are not doing this in a safe way this function can be reused
--         to change the label of some random node. This happens because when adding
--         to a map a key that already exists the previous key gets replaced.
addState :: (Ord s, Ord i, Ord a, Ord prop) =>
            DTS s i prop a ->
            s ->
            [[prop]] ->
            Bool ->
            DTS s i prop a
addState dts s props isInitial =
  DTS {states             = (states dts) `S.union` (S.fromList [s]),
       actions            = actions dts,
       initialStates      = if isInitial
                            then (initialStates dts) `S.union` (S.fromList [s])
                            else initialStates dts,
       propSymbols        = propSymbols dts,
       labelingFunction   = M.insert s (map S.fromList props) (labelingFunction dts),
       transitionRelation = transitionRelation dts}

-- | Input: a DTS, two states and an action
--   Output: a DTS with the action added as predicted.
--   NOTE:  We do not check if the transition is legal
--          We do not check if the action is an action of the system
addTransition :: (Ord s, Ord i, Ord a, Ord prop) =>
                 DTS s i prop a ->
                 s -> -- departure state
                 s -> -- arrival state
                 a -> -- action that causes the transition
                 DTS s i prop a -- returned transition system
addTransition dts departure arrival action =
  DTS {
      states = states dts,
      actions = actions dts,
      initialStates = initialStates dts,
      propSymbols = propSymbols dts,
      labelingFunction = labelingFunction dts,
      transitionRelation = M.insert (departure, action) arrival (transitionRelation dts)
      }
-- Just some test instances --
t = DTS {states = S.fromList [1, 2, 3, 4],
        actions = M.fromList [(1, S.fromList ["a", "b"]), (2, S.fromList ["a", "c"])],
        initialStates = S.fromList [1, 4],
        propSymbols = M.fromList [
            (1, S.fromList ["p1", "q1"]),
            (2, S.fromList ["p2", "q2'"])
                    ],
        labelingFunction = M.fromList [
            (1, [S.fromList ["p1"], S.fromList ["q2"]]),
            (2, [S.fromList ["p1"], S.fromList []]),
            (3, [S.fromList [], S.fromList ["q2"]]),
            (4, [S.fromList [], S.fromList []])
                    ],
        transitionRelation = M.fromList []}
