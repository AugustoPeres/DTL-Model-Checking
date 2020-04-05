module DTS (DTS, )
where

import Data.List ((\\))
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
                          labelingFunction   :: M.Map (s, i) (S.Set prop),
                          transitionRelation :: M.Map (s, a) s
                          } deriving (Show)
-- -----------------------------------------------------------------------------
-- END: Definition of destributed transition system
-- -----------------------------------------------------------------------------

instance (Show s, Show prop, Show a, Ord s) => FiniteGraphRepresentable (DTS s i prop a) where
  toGraphviz system =
    "Digraph {\n" ++
    --foldr (\a b -> b ++ show a ++ " [label =" ++ (show $ getter a) ++ ",shape=box]") "" sts ++
    "}"
    where sts = states system
          l = labelingFunction system
          -- getter s = fromJust $ (M.lookup s l)


-- | Input: Receives a distributed transiotion system a state, a list with local valuations
--          and a boolean
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
            [(i, S.Set prop)] ->
            Bool ->
            DTS s i prop a
addState dts s props isInitial =
  DTS {states             = (states dts) `S.union` (S.fromList [s]),
       actions            = actions dts,
       initialStates      = if isInitial
                            then (initialStates dts) `S.union` (S.fromList [s])
                            else initialStates dts,
       propSymbols        = propSymbols dts,
       labelingFunction   = foldr (\a b -> M.insert (s, fst a) (snd a) b) (labelingFunction dts) props,
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
      states             = states dts,
      actions            = actions dts,
      initialStates      = initialStates dts,
      propSymbols        = propSymbols dts,
      labelingFunction   = labelingFunction dts,
      transitionRelation = M.insert (departure, action) arrival (transitionRelation dts)
      }


-- | Input: A DTS , 2 staes and an action
--   Output: A DTS with a transition added.
--   NOTE: In this function we check if we can add that transition
--         If that is not the case we simply return the transition
--         system that was given as input.
addTransitionSafe :: (Ord s, Ord i, Ord a, Ord prop) =>
                     DTS s i prop a ->
                     s ->
                     s ->
                     a ->
                     DTS s i prop a
addTransitionSafe dts departure arrival action =
  if isTransitionAllowed dts departure arrival action
  then addTransition dts departure arrival action
  else dts


-- | Input: A DTS, two states and an action
--   Output: True iff that transition is allowed
--   NOTE: A transition is allowed if:
--         1. The action is not an action of agent i then the propositional
--            symbols cannot change
--         2. If the departure state doesn't have already a transition by that action.
--   In summary this checks if a condition can be added
isTransitionAllowed :: (Ord a, Ord i, Ord s, Ord prop) =>
                       DTS s i prop a ->
                       s ->
                       s ->
                       a ->
                       Bool
isTransitionAllowed dts departure arrival action =
  all (\x -> l M.! (departure, x) == l M.! (arrival, x)) agentsNotEvolving
  &&
  -- checks condition 2. --
  (departure, action) `notElem` (M.keys (transitionRelation dts))
  where agentsNotEvolving = filter (\x -> action `S.notMember` (acts M.! x)) agents
        agents = M.keys (acts)
        acts = actions dts
        l = labelingFunction dts


-- | Input: A DTS
--   Output: A list with all the strongly connected components of the system
--   Method : Kosaraju
--   NOTE: Because of S.elemAt 0 this will raise an error in the case where
--         a transition system without any states.
kosaraju :: (Ord s, Ord i, Ord prop, Ord a) =>
            DTS  s i prop a ->
            [[s]]
kosaraju dts =
  helper ord [] []
  where ord = makeOrder $ dfs dts [S.elemAt 0 sts] [] True
        makeOrder ord
          | sts == S.fromList ord = ord
          | otherwise = makeOrder ((dfs dts [head $ lsts \\ ord] ord True\\ ord) ++ ord)
        lsts = S.toList sts
        sts = states dts
        aT = transpose dts
        helper order visited scc
          | null order = scc
          | otherwise = helper (order \\ b) (b ++ visited) (b:scc)
          where b = dfs aT [head order] [] True \\ visited


-- | Input: A DTS
--   Output: The transposed DTS
transpose :: (Ord s, Ord i, Ord prop, Ord a) =>
             DTS s i prop a ->
             DTS s i prop a
transpose dts =
  DTS { states = states dts,
        actions = actions dts,
        initialStates = initialStates dts,
        propSymbols = propSymbols dts,
        labelingFunction = labelingFunction dts,
        transitionRelation = M.foldrWithKey (\k a b -> M.insert (a, snd k) (fst k) b)
                                           M.empty
                                           (transitionRelation dts)}
-- | Input: A DTS, a Q and, list of visited states and a boolean value
--   Output: A list with all the states that can be visited
--           from all the states in the Q over the transition system given
--   NOTE: When the boolean value is True we assume that s reaches s even when no
--         self loop exists
dfs :: (Ord a, Ord i, Ord s, Ord prop) =>
       DTS s i prop a ->
       [s] -> -- the original list of states given
       [s] -> -- the returned list of visited states
       Bool ->
       [s]
dfs dts [] v _ = v
dfs dts (x:xs) v b
  | b = dfs dts ([s | s <- neigs, s `notElem` (x:v)] ++ xs) newvisited True
  | otherwise = dfs dts ([s | s <- neigs, s `notElem` (x:v)]) v True
  where neigs = getNeighbours dts x
        newvisited = if x `elem` v then v else v ++ [x]


-- | Input: A DTS and a state.
--   Output: A list with all the nodes directly acced from that node
getNeighbours :: (Ord s , Ord i, Ord a, Ord prop) =>
                 DTS s i prop a ->
                 s ->
                 [s]
getNeighbours dts state =
  M.foldrWithKey f [] tr
  where tr = transitionRelation dts
        f k a b = (if fst k == state then b ++ [a] else b)
-- Just some test instances --
t = DTS {states = S.fromList [1, 2, 3, 4],
        actions = M.fromList [(1, S.fromList ["a", "b"]), (2, S.fromList ["a", "c"])],
        initialStates = S.fromList [1, 4],
        propSymbols = M.fromList [
            (1, S.fromList ["p1", "q1"]),
            (2, S.fromList ["p2", "q2'"])
                    ],
        labelingFunction = M.fromList [
                                      ((1, 1), S.fromList ["p"]),
                                      ((1, 2), S.fromList ["q"]),
                                      ((2, 1), S.fromList ["p"]),
                                      ((2, 2), S.fromList []),
                                      ((3, 1), S.fromList []),
                                      ((3, 2), S.fromList ["q"]),
                                      ((4, 1), S.fromList []),
                                      ((4, 2), S.fromList [])
                                      ],
        transitionRelation = M.fromList []}


tKosBug = DTS {states = S.fromList [1, 2, 3, 4],
        actions = M.fromList [(1, S.fromList ["a", "b"]), (2, S.fromList ["a", "c"])],
        initialStates = S.fromList [1, 4],
        propSymbols = M.fromList [
            (1, S.fromList ["p1", "q1"]),
            (2, S.fromList ["p2", "q2'"])
                    ],
        labelingFunction = M.fromList [
                                      ((1, 1), S.fromList ["p"]),
                                      ((1, 2), S.fromList ["q"]),
                                      ((2, 1), S.fromList ["p"]),
                                      ((2, 2), S.fromList []),
                                      ((3, 1), S.fromList []),
                                      ((3, 2), S.fromList ["q"]),
                                      ((4, 1), S.fromList []),
                                      ((4, 2), S.fromList [])
                                      ],
        transitionRelation = M.fromList [((3, "a"), 4), ((4, "a"), 1)]}
