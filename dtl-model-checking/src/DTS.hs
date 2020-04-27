module DTS (DTS (..), getAllActions, getLabel, getAgents,
            getPropSymbolsAgent, createFromStates, addStateLabel,
            addToInitialStates, addTransitionSafe, addActionAgent,
            getActionsAgent, isTransitionOfSystem, kosaraju,
            isReachableFromStates, deleteStates, deleteDeadStates,
            getNeighbours, deleteWhileDeadStates, dfs, addTransition,
            subTransitionSystem, generateDTSFromStdGen, addState,
            fullSimplify, deleteUnreachableStates, shortestPath,
            shortestPathFromInitialState, shortestPathFromInitialStateList,
            subDTSWithInitialStates, empty, bfsWithStopCondition,
            isReachableFromStates')
where

import           CommonTypes
import           Data.List     (subsequences, union, (\\))
import qualified Data.Map.Lazy as M
import           Data.Maybe
import qualified Data.Set      as S
import           System.Random
import           Utils         (bernoulli)
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

instance (Show s, Show prop, Show a, Ord s, Ord prop) => FiniteGraphRepresentable (DTS s i prop a) where
  toGraphviz system =
    "Digraph {\n node [shape = box]\n" ++
    -- labeling the states  with the respective propositional symbols --
    M.foldrWithKey (\k x y -> y ++ show x ++ " [label = \""
                                ++ show k ++ ": " ++
                                (show $ getLabel system k) ++ "\"];\n")
                   ""
                   stateMap
   ++
   -- making the transition relation a string --
   M.foldrWithKey (\k x y -> y ++
                          foldr (\x' y' -> y' ++
                                              show (stateMap M.! fst k) ++ "->" ++
                                              show (stateMap M.! x') ++
                                              "[label = \"" ++ show (snd k) ++ "\"];\n")
                                   ""
                                   x)
                  ""
                  tr
   ++
    "}"
    where sts = states system
          tr = transitionRelation system
          stateMap = M.fromList (zip (S.toList sts) [1..])


-- | This is just a constant, representing an empty trnasition system
empty :: DTS s i prop a
empty = DTS S.empty M.empty S.empty M.empty M.empty M.empty

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
addStateLabel :: (Ord s , Ord i, Ord a, Ord prop) =>
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


-- | Input: A transition system and a list of states
--   Output: A transition system with all the states deleted
--           except the ones in the that list and in the shortest
--           path from an initial state to that state in a list.
--           If there is no such path we simply return the sub transition system
subDTSWithInitialStates :: (Ord a, Ord i, Ord s, Ord prop) =>
                           DTS s i prop a ->
                           [s] ->
                           DTS s i prop a
subDTSWithInitialStates dts list
  | isJust pathKept =
    subTransitionSystem dts (list `union` fromJust pathKept)
  | otherwise = subTransitionSystem dts list
  where pathKept = shortestPathFromInitialStateList dts list


-- | Input: A transitions system and a set of states
--   Output: A transition system with all the other states deleted
subTransitionSystem :: (Ord a, Ord i, Ord s, Ord prop) =>
                       DTS s i prop a ->
                       [s] ->
                       DTS s i prop a
subTransitionSystem dts list = deleteStates dts (S.toList (states dts) \\ list)

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
      (M.foldrWithKey (\k _ y -> if fst k `S.member` rmsets
                                        then M.delete k y
                                        else M.adjust (\\ list) k y)
                             tr
                             tr)
  where rmsets = S.fromList list
        l      = labelingFunction dts
        keysLb = M.keys l
        tr = transitionRelation dts


-- | Input: A DTS
--   Output: A DTS resulting from successively removing dead states
--   after removing states that can't be reached from initial states
fullSimplify :: (Ord a, Ord i, Ord s, Ord prop) =>
                DTS s i prop a ->
                DTS s i prop a
fullSimplify dts
  | null unreachStates && null deadStates = dts
  | null deadStates    = fullSimplify $
                         deleteWhileDeadStates (deleteStates dts unreachStates)
  | null unreachStates = fullSimplify $
                         deleteUnreachableStates (deleteStates dts deadStates)
  | otherwise = fullSimplify $ (deleteWhileDeadStates $ deleteUnreachableStates dts)
  where unreachStates = S.toList $
                        S.filter (\x -> not $ isReachableFromStates' dts x ists) sts
                        S.\\
                        initialStates dts
        deadStates    = S.toList $
                        S.filter (null . getNeighbours dts) sts
        sts           = states dts
        ists          = S.toList $ initialStates dts

-- | Input: A DTS
--   Output: A DTS with all states that cannot be reached
--           from an initial state removed
deleteUnreachableStates :: (Ord a, Ord i, Ord s, Ord prop) =>
                           DTS s i prop a ->
                           DTS s i prop a
deleteUnreachableStates dts =
  deleteStates dts unreachableStates
  where unreachableStates = S.toList $
                            S.filter (\x -> not $ isReachableFromStates' dts x ists') sts
                            S.\\
                            ists
        sts   = states dts
        ists  = initialStates dts
        ists' = S.toList $ ists


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


-- | Input: A DTS and a list of node
--   Output: The shortest path from any initial state to
--           any of the nodes in the provided list
shortestPathFromInitialStateList :: (Ord a, Ord i, Ord s, Ord prop) =>
                                    DTS s i prop a ->
                                    [s] ->
                                    Maybe [s]
shortestPathFromInitialStateList dts list
  | (not . null) aux =
    Just $ [head aux]
  | otherwise =
    if null shortestPaths
      then Nothing -- case were no path exists
      else helper (head $ shortestPaths) (tail shortestPaths)
  where shortestPaths = filter isJust $
                               map (shortestPathFromInitialState dts) list
        inits = initialStates dts
        aux = dropWhile (`S.notMember` inits) list
        helper v [] = v
        helper v (x:xs)
          | fmap length v > fmap length x = helper x xs
          | otherwise = helper v xs


-- | Input: A DTS and a node
--   Output: Maybe the shortest path from any
--           initial state to that node
--   NOTE: If the state is an initial state we just return it.
shortestPathFromInitialState :: (Ord a, Ord i, Ord s, Ord prop) =>
                                DTS s i prop a ->
                                s ->
                                Maybe [s]
shortestPathFromInitialState dts s
  | s `S.member` inits = Just [s]
  | otherwise =
    if null paths
      then Nothing
      else helper (head $ paths) (tail paths)
  where paths    = filter isJust
                          (map (\x -> shortestPath dts x s)
                              (S.toList $ inits))
        inits = initialStates dts
        helper v [] = v
        helper v (x:xs)
          | fmap length v > fmap length x = helper x xs
          | otherwise = helper v xs


-- | Input: A DTS, Two nodes
--   Output: The shortest path from node 1 to node 2
--           represented as a list of nodes
shortestPath :: (Ord a, Ord i, Ord s, Ord prop) =>
                DTS s i prop a ->
                s ->
                s ->
                Maybe [s]
shortestPath dts s1 s2 =
  go [] [[s1]]
  where go _ [] = Nothing -- this is the case were we find no path
        go v (x:xs)
          | null nextNodes = go (currNode:v) xs
          | any (==s2) nextNodes = Just $ x ++ [s2]
          | otherwise = go (currNode:v)
                           (foldr (\x' y -> if (x' `notElem` v) && (not $ any (x'`elem`) xs)
                                    then y ++ [x++[x']]
                                    else y)
                                    xs
                                  nextNodes)
          where nextNodes = getNeighbours dts currNode -- raises error on empty
                currNode = last x

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
dfs _ [] v _ = v
dfs dts (x:xs) v b
  | length v == max = v -- stopage condition for graphs with high degree
  | b = dfs dts ([s | s <- neigs, s `notElem` (x:v)] ++ xs) newvisited True
  | otherwise = dfs dts ([s | s <- neigs, s `notElem` (x:v)]) v True
  where neigs = getNeighbours dts x
        newvisited = if x `elem` v then v else v ++ [x]
        max = length $ S.toList (states dts)


isReachableFromStates :: (Ord a, Ord i, Ord s, Ord prop) =>
                         DTS s i prop a ->
                         s -> -- state we want to check
                         [s] -> -- list of possible departure states
                         Bool
isReachableFromStates dts state list = any (\x -> state `elem` dfs dts [x] [] False) list



isReachableFromStates' :: (Ord a, Ord i, Ord s, Ord prop) =>
                         DTS s i prop a ->
                         s -> -- state we want to check
                         [s] -> -- list of possible departure states
                         Bool
isReachableFromStates' dts state list =
  any (\x -> state
             `elem`
              bfsWithStopCondition dts
                                   [x]
                                   [ ]
                                   (\x1 _ -> state `elem` x1)
      ) list


-- | Input: A DTS a Q, a list of visited states and a function
--          (q -> visited -> boll) that works as a stopage
--          condition
--   Output: The visited states until the stopage condition is met
--   NOTE: When the stopage condition is met we return all the states
--         that were already visited together with the ones in the q
bfsWithStopCondition :: (Ord a , Ord i, Ord s, Ord prop) =>
                        DTS s i prop a ->
                        [s] -> -- q
                        [s] -> -- visited states
                        ([s] -> [s] -> Bool) -> -- the stopage condition
                        [s]
bfsWithStopCondition _ [] v _ = v
bfsWithStopCondition dts q@(x:xs) v f
  | f q v = v `union` q
  | otherwise = bfsWithStopCondition dts
                                     (xs ++ ((new \\ v) \\q ))
                                     (v ++ [x])
                                     f
  where new = getNeighbours dts x

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


-- -----------------------------------------------------------------------------
-- BEGIN: IO () Functions
-- -----------------------------------------------------------------------------
-- This contains IO fuctions used for example to read systems from input or to
-- generate random transition systems

-- | Input: A list of agents, propositional symbols for the agents
--          actions for the agents, an stdgen, and two float denoting a probability.
--          The first probablity refer to the probability of a state being an initial
--          state, while the other refers to the probablity of creating edges.
--   Output: A transitions systems generated for that that StdGen
--   Note: The number of states will always be 2^(number of propositional symbols)
generateDTSFromStdGen :: (Ord prop, Ord a) =>
                         Int -> -- ^ number of agents
                         [[prop]] -> -- ^list with prop symbols of each agent
                         [[a]] -> -- ^ list with all the actions
                         StdGen ->
                         Float ->
                         Float ->
                         DTS Int Int prop a
generateDTSFromStdGen n props actions stdgen p1 p2 =
  -- adding the transitions --
  foldr (\x y -> addTransitionSafe y (fst' x) (snd' x) (thr' x))
        -- adding the state labels --
        (foldr (\x y -> addStateLabel y (fst' x) (snd' x) (thr' x))
              -- adding the states and the initial states --
              (foldr (\x y -> addToInitialStates y x)
                     (DTS (S.fromList sts)
                          actmap
                          S.empty
                          (M.fromList $ zip agents (map (S.fromList) props))
                          M.empty
                          M.empty)
                     init)
              -- adding the states and the initial states --
              labels)
        -- adding the state labels --
        trnsToBeAdded
  -- adding the transition --
  where sts  = [1..(2^nprops)]
        agents = [1..n]
        nprops = length $ concat props
        acts = concat actions
        actmap = M.fromList [(i, S.fromList $ actions!!(i - 1)) | i <- agents]
        -- here we create the initial states --
        -- we make sure that state number 1 is always an initial state --
        init = map snd (filter fst (zip (bernoulli stdgen p1) sts)) `union` [1]
        -- here we create the labeling function --
        -- mapping the states to the possible label indexes --
        possiblePairsAgent i = [(i - 1, y) | y <- [0..((2^(length $ props!!(i - 1))) - 1)]]
        allPairsAgents = map possiblePairsAgent agents
        allcombinations = helper allPairsAgents [[]]
        sm = M.fromList $ zip sts allcombinations
        labels = M.foldrWithKey (\k x y -> y ++ foldr (\x' y' -> y' ++ [(k, fst x', p (fst $ snd x') (snd $ snd x'))])
                                                      []
                                                      (zip agents x))
                                []
                                sm
        p i s = ((map subsequences props)!!(i))!!(s)
        -- here we create the transitions that should be added --
        -- we zipp with a list of booleans that determine of the
        -- trnasition will be added or not --
        transits = zip (bernoulli stdgen p2) [(s1, s2, act) | s1  <- sts,
                                                             s2  <- sts,
                                                             act <- acts]
        trnsToBeAdded = map snd (filter fst transits)
        thr' (_, _, b) = b
        snd' (_, b, _) = b
        fst' (b, _, _) = b
        helper [x] b    = [b' ++ [x'] | b' <- b, x' <- x]
        helper (x:xs) b = helper xs [b' ++ [x'] | b' <- b , x' <- x]


-- -----------------------------------------------------------------------------
-- END: IO () Functions
-- -----------------------------------------------------------------------------



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
