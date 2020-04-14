module DTS (DTS (..), getAllActions, getLabel, getAgents,
            getPropSymbolsAgent, createFromStates, addStateLabel,
            addToInitialStates, addTransitionSafe, addActionAgent,
            getActionsAgent, isTransitionOfSystem, kosaraju,
            isReachableFromStates, deleteStates, deleteDeadStates,
            getNeighbours, deleteWhileDeadStates, dfs)
where

import Data.List ((\\), union)
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
                          transitionRelation :: M.Map (s, a) [s]
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


-- | Input: A list of states
--   Output: An empty transition system with only those states
createFromStates :: (Ord s, Ord i, Ord prop, Ord a) =>
                    [s] ->
                    DTS s i prop a
createFromStates list =
  DTS { states             = S.fromList list,
        actions            = M.empty,
        initialStates      = S.empty,
        propSymbols        = M.empty,
        labelingFunction   = M.empty,
        transitionRelation = M.empty}


-- | Input: A list of states and a dts
--   Output: A new dts with the states added to the initial states
addToInitialStates :: (Ord s, Ord i, Ord prop, Ord a) =>
                      DTS s i prop a ->
                      s ->
                      DTS s i prop a
addToInitialStates dts state =
  DTS { states             = states dts,
        actions            = actions dts,
        initialStates      = initialStates dts `S.union` S.fromList [state],
        propSymbols        = propSymbols dts,
        labelingFunction   = labelingFunction dts,
        transitionRelation = transitionRelation dts}


-- | Input: A dts, a state, ann agent, and a label
--   Output: A new dts with that local label added
--   NOTE: this is not safe. Moreover a label for an existing state
--         might be replaced
addStateLabel :: (Ord s, Ord i, Ord prop) =>
                 DTS s i prop a ->
                 s ->
                 i ->
                 [prop] ->
                 DTS s i prop a
addStateLabel dts state agent list =
  DTS { states             = states dts,
        actions            = actions dts,
        initialStates      = initialStates dts,
        propSymbols        = propSymbols dts,
        labelingFunction   = M.insert (state, agent) (S.fromList list) (labelingFunction dts),
        transitionRelation = transitionRelation dts}

-- | Input: a dts, an action, an agent
--   Output: a dts with that action added for that agent
addActionAgent :: (Ord i, Ord a) =>
                  DTS s i prop a ->
                  a ->
                  i ->
                  DTS s i prop a
addActionAgent dts action agent =
  DTS { states             = states dts,
        actions            = M.insert agent (newActions) (actions dts),
        initialStates      = initialStates dts,
        propSymbols        = propSymbols dts,
        labelingFunction   = labelingFunction dts,
        transitionRelation = transitionRelation dts}
  where newActions = S.union (fromMaybe S.empty (actions dts M.!? agent)) (S.fromList [action])


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
      transitionRelation = M.insertWith (union)
                                        (departure, action)
                                        [arrival]
                                        (transitionRelation dts)
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


-- Input: A DTS and a a list of states
-- Output: A DTS with that state removed
deleteStates :: (Ord a, Ord i, Ord s, Ord prop) =>
                DTS s i prop a ->
                [s] ->
                DTS s i prop a
deleteStates dts list =
  DTS (states dts `S.difference` (rmsets))
      (actions dts)
      (initialStates dts `S.difference` (rmsets))
      (propSymbols dts)
      -- we must delete the labels of the deleted states --
      (foldr (\x y -> if fst x `S.member` rmsets then M.delete x y else y) l keysLb)
      -- now we delete from the transition function , this is more complicated
      -- because we must also delete arrows going to those states --
      (M.foldrWithKey (\k x y -> if fst k `S.member` rmsets
                                        then M.delete k y
                                        else M.adjust (\\ list) k y)
                             tr
                             tr)
  where rmsets = S.fromList list
        l      = labelingFunction dts
        keysLb = M.keys l
        tr = transitionRelation dts


-- | Input: A DTS
--   Output: A DTS from whcih all dead states are removed in succession
--           until no more dead states are present in the system
deleteWhileDeadStates :: (Ord a, Ord i, Ord s, Ord prop) =>
                         DTS s i prop a ->
                         DTS s i prop a
deleteWhileDeadStates dts
  | null deadStates = dts
  | otherwise = deleteWhileDeadStates (deleteStates dts deadStates)
  where deadStates = S.toList $ S.filter (null . getNeighbours dts) (states dts)


-- | Input: A DTS
--   Output: A DTS with all the states that have no outgoing arrows removed
deleteDeadStates :: (Ord a, Ord i, Ord s, Ord prop) =>
                    DTS s i prop a ->
                    DTS s i prop a
deleteDeadStates dts =
  deleteStates dts deadStates
  where deadStates = S.toList $ S.filter (null . getNeighbours dts) (states dts)

-- | Input: A DTS, two states and an action
--   Output: True iff that transition is allowed
--   NOTE: A transition is allowed if:
--         1. The action is not an action of agent i then the propositional
--            symbols cannot change
--         DEPRECATED: 2. If the departure state doesn't have already a
--                     transition by that action. now we allow for non determinism
--                     in the action. This is because the model checking problem
--                     requires so for the dot product. The user should be careful
--                     when creating deterministic transition systems.
--   In summary this checks if a condition can be added
isTransitionAllowed :: (Ord a, Ord s, Eq prop, Ord i) =>
                       DTS s i prop a ->
                       s ->
                       s ->
                       a ->
                       Bool
isTransitionAllowed dts departure arrival action =
  all (\x -> l M.! (departure, x) == l M.! (arrival, x)) agentsNotEvolving
  where agentsNotEvolving = filter (\x -> action `S.notMember` (acts M.! x)) agents
        agents = M.keys (acts)
        acts = actions dts
        l = labelingFunction dts


-- | Input: A dts, two states and an action
--   Output: True if it is an action of the agent
isTransitionOfSystem :: (Ord s, Ord a) =>
                        DTS s i prop a ->
                        s ->
                        s ->
                        a ->
                        Bool
isTransitionOfSystem dts s1 s2 act =
  if goal == Nothing
  then False
  else s2 `elem` (fromJust goal)
  where goal = (transitionRelation dts)M.!?(s1, act)

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
        transitionRelation =
          M.foldrWithKey (\k x y -> foldr (\x' y' -> M.insertWith
                                                    (union)
                                                    (x',snd k)
                                                    [fst k]
                                                    y')
                                          y
                                          x
                         )
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


isReachableFromStates :: (Ord a, Ord i, Ord s, Ord prop) =>
                         DTS s i prop a ->
                         s -> -- state we want to check
                         [s] -> -- list of possible departure states
                         Bool
isReachableFromStates dts state list = any (\x -> state `elem` dfs dts [x] [] False) list


-- | Input: A DTS and a state.
--   Output: A list with all the nodes directly acced from that node
getNeighbours :: (Ord s , Ord i, Ord a, Ord prop) =>
                 DTS s i prop a ->
                 s ->
                 [s]
getNeighbours dts state =
  M.foldrWithKey f [] tr
  where tr = transitionRelation dts
        f k a b = (if fst k == state then b ++ a else b)


-- | Input: A DTS
--   Output: All the actions in a list regardless of agent
getAllActions :: (Ord s, Ord a) =>
                 DTS s i prop a ->
                 [a]
getAllActions dts =
  S.toList $
  M.foldr (S.union) S.empty (actions dts)

-- | Input: A DTS, and an agent
--   Output: All the actions for that agent as a list
getActionsAgent :: (Ord a, Ord i) =>
                   DTS s i prop a ->
                   i ->
                   [a]
getActionsAgent dts agent =
  S.toList $ fromMaybe S.empty ((actions dts)M.!?agent)

-- | Input: A DTS and a state
--   Output: The label for the state as a concatenated list
getLabel :: (Ord s, Ord prop) =>
            DTS s i prop a ->
            s ->
            [prop]
getLabel dts state =
  S.toList $
  M.foldrWithKey (\k x y -> if fst k == state then S.union x y else y)
                 S.empty
                 (labelingFunction dts)


-- | Input: A dts and an agent
--   Output: A list with all the propositional symbols from that agent
getPropSymbolsAgent :: (Ord i) =>
                       DTS s i prop a ->
                       i ->
                       [prop]
getPropSymbolsAgent dts agent =
  S.toList $ fromMaybe S.empty ((propSymbols dts) M.!? agent)
-- | Input: A DTS
--   Output: The agents of the system.
--   NOTE: WE assume that the mappings in the system are complete, i.e,
--         the keys in the maps envolving agents encompasse all keys.
getAgents :: (Ord i) =>
             DTS s i prop a ->
             [i]
getAgents dts = M.keys (propSymbols dts)
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
        transitionRelation = M.fromList [((3, "a"), [4]), ((4, "a"), [1])]}
