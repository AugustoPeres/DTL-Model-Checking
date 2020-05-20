{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
module AutomataTheoreticApproach (AutomataCounterExample(..),
                                  modelCheck, modelCheckWithCounterExamples, makeComplementaryGNBA,
                                  convertGNBAToNBA, dotProductParticullarCase,
                                  modelCheckOneCounterExample)
  where

import           CommonTypes
import           Data.List     (union, (\\))
import qualified Data.Map.Lazy as M
import qualified Data.Set      as S
import qualified DTLFormula    as F
import qualified DTS           as T
import qualified GNBA          as G
import qualified Ielementary   as I
import qualified NBA           as N
--import System.Random
import Data.Maybe
--import ExampleInstances

-- The data marker is just used to mark the states.
-- Recall from the definition in the thesis that states
-- marked with Upsilon are used to express runs were the
-- non satisfaction happens finitely often.
data Marker = Upsilon | None deriving (Eq, Ord, Show)

-- Now we can represent the states of the GNBA as tuples of marked sets
-- of formulas, In fact they are only propositional symbols, but to simplify
-- we use SOF
type GNBAState = [(I.SOF, Marker)]

-- The alphabet symbols consists of actions concatenated with actions
-- Both are represented here as strings
type Action = String
type AlphabetSymbol = (I.SOF, Action)

data AutomataCounterExample s = ACE { dotProductWitness  :: T.DTS (s, N.State) Int N.State Action
                                    , sccWitness         :: T.DTS (s, N.State) Int N.State Action
                                    , counterExample     :: T.DTS s Int F.Formula Action
                                    , fairnessConstraint :: [(s, N.State)]}
                                deriving (Show)
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

-- -----------------------------------------------------------------------------
-- BEGIN: Here we instance show for our types, this makes debuging much easir
-- -----------------------------------------------------------------------------

instance {-# OVERLAPPING #-} Show GNBAState where
    show [] = ""
    show (x:xs) =
      "{" ++
      S.foldr (\a b -> b ++ show a ++ ",") "" (fst x ) ++ (show (snd x)) ++
      "}\\n" ++
      show xs

instance {-# OVERLAPPING #-} Show Action where
  show a = a

instance {-# OVERLAPPING #-} Read Action where
  readsPrec _ act = [(id act, "")]

instance {-# OVERLAPPING #-} Show AlphabetSymbol where
  show sigma = "<" ++
               S.foldr (\a b -> b ++ show a ++ ",") "" (fst sigma) ++
               show (snd sigma) ++
               ">"
-- -----------------------------------------------------------------------------
-- END: Here we instance show for our types, this makes debuging much easir
-- -----------------------------------------------------------------------------


-- | Input: A transition system, a DTL formula, an integer
--   Output: A ModelCheckingAnswer [(T,[s])] Where this list contains tuples
--           of transition systems with fairness conditons that correspond to
--           the counter examples found.
--   NOTE: We full simplify the automatons as we are not interested in
--         checking anything with finite paths and removing unreachable
--         states does not cause the problem to change
modelCheckWithCounterExamples :: Ord s =>
                                T.DTS s Int F.Formula Action ->
                                F.GlobalFormula ->
                                Int ->
                                ModelCheckingAnswer [AutomataCounterExample s]
modelCheckWithCounterExamples dts alpha n =
  go relevant Satisfies
  where gComp = makeComplementaryGNBA alpha n actions
        actions = map (T.getActionsAgent dts) [1..n]
        dts' = T.fullSimplify dts
        -- now we convert to a NBA --
        nbaComp = convertGNBAToNBA gComp (G.getAlphabet gComp)
        fs = N.finalStates nbaComp
        -- now we make the dot product and then remove irrelevant states --
        clo = F.closureFormula alpha n
        tDotnbaComp = T.fullSimplify $ dotProductParticullarCase dts' nbaComp clo
        -- now the states that we are interested for the persistence --
        persStates = S.filter (\x -> (head $ T.getLabel tDotnbaComp x) `elem` fs)
                              (T.states tDotnbaComp)
        -- strongly connected componets --
        scc = T.kosaraju tDotnbaComp
        -- strongly connected componets that can be reached --
        relevant = filter (\x -> any (\y -> any (`elem` x) (T.getNeighbours tDotnbaComp y))
                                         x)
                              scc
        -- the fuction go --
        --go :: (Ord s) => [[(s, N.State)]] -> ModelCheckingAnswer [[s]] -> ModelCheckingAnswer [[s]]
        go [] b = b
        go (x:xs) acc = if any (\state -> S.member state persStates) x
          then go xs (acc <>
                      CounterExample [ACE (exemp)
                                          (T.subTransitionSystem tDotnbaComp x)
                                          (T.subDTSWithInitialStates dts' (S.toList $ S.map fst (T.states(exemp))))
                                          (filter (`elem` persStates) x)])
          else go xs acc
          where exemp = T.subDTSWithInitialStates tDotnbaComp x


-- | Input: A transition system, A DTL formula and an integer
--   Output: A model checking solution with just one counter example
--           This counter example consists of the first scc with a final state.
--           Then we output the path from an initial state to that state and the
--           shortest path from that node to itself.
modelCheckOneCounterExample :: Ord s =>
                               T.DTS s Int F.Formula Action ->
                               F.GlobalFormula ->
                               Int ->
                               ModelCheckingAnswer ([(s, N.State)], [(s, N.State)])
modelCheckOneCounterExample dts alpha n =
  go (S.toList persStates)
  where gComp = makeComplementaryGNBA alpha n actions
        actions = map (T.getActionsAgent dts) [1..n]
        -- now we convert to a NBA --
        nbaComp = N.fullSimplify $ convertGNBAToNBA gComp (G.getAlphabet gComp)
        fs = N.finalStates nbaComp
        -- now we make the dot product and then remove irrelevant states --
        clo = F.closureFormula alpha n
        tDotnbaComp = T.fullSimplify $
                      dotProductParticullarCase (T.fullSimplify dts) nbaComp clo
        -- now the states that we are interested for the persistence --
        persStates = S.filter (\x -> (head $ T.getLabel tDotnbaComp x) `elem` fs)
                              (T.states tDotnbaComp)
        go [] = Satisfies
        go (state:xs) =
          if isNothing path1
          then go xs
          else CounterExample (fromJust $ T.shortestPathFromInitialState tDotnbaComp state, fromJust path1)
          where path1 = T.shortestPath tDotnbaComp state state


-- | Input: A transition system, a DTL formula and an integer.
--   Output: Yes iff the transition system satisfies the formula
--   This is the MAIN function on the module.
--   NOTE: We force the transition system to have:
--            1. Integer agents
--            2. Propositional Symbols of type formula
--            3. Actions of type action
--         because that was how we defined the DTL formulas module
--         Therefore that must be the language that is accepted by the automaton
--         therefore the transition system must be of all of these types
--   NOTE: We full simplify the transition system because we are not interested in
--         model checking systems with finite paths. All states must be abbe to make
--         transitions.
modelCheck :: Ord s =>
              T.DTS s Int F.Formula Action ->
              F.GlobalFormula ->
              Int -> -- number of agents
              Bool
modelCheck dts alpha n =
  not $
    any (\x -> T.isReachableFromStates' tDotnbaComp x [x]) persStates
  where gComp = makeComplementaryGNBA alpha n actions
        actions = map (T.getActionsAgent dts) [1..n]
        -- now we convert to a NBA --
        nbaComp = N.fullSimplify $ convertGNBAToNBA gComp (G.getAlphabet gComp)
        fs = N.finalStates nbaComp
        -- now we make the dot product and then remove irrelevant states --
        clo = F.closureFormula alpha n
        tDotnbaComp = T.fullSimplify $
                      dotProductParticullarCase (T.fullSimplify dts) nbaComp clo
        -- now the states that we are interested for the persistence --
        persStates = S.filter (\x -> (head $ T.getLabel tDotnbaComp x) `elem` fs)
                              (T.states tDotnbaComp)
        -- strongly connected componets --
        --scc = T.kosaraju tDotnbaComp



-- -----------------------------------------------------------------------------
-- BEGIN: Converting the GNBA to the NBA used in model checking
-- -----------------------------------------------------------------------------

-- | Input: An GNBA for a given language, the alphabet of the automaton
--   Output: The NBA for the same language
--   METHOD: Principles of model checking
--   NOTE: isTransitionAllowed might not work when there are no acceptance sets
--   NOTE: This could be more efficient if I did not filter through all possible
--         transition. Instead of filtering through all possible transitions I
--         could construction delta for the NBA directly. This would prevent
--         several map lookups to check weather or not a transition is possible.
--         Might even be easier to write.
convertGNBAToNBA :: (Eq s, Eq a, Ord s) => G.GNBA s a -> [a] -> N.NBA a
convertGNBAToNBA g alphabet =
  -- 4. finally adding the transitions --
  foldr (\x b -> N.addTransition b (fst $ fst x) (snd x) (snd $ fst x))
        -- 3. addint the final states --
        (foldr (\x b -> N.addFinalState b x)
              -- 2. adding the inicial states --
              (foldr (\x b -> N.addInitialState b x)
                    -- first we add the states to an empty automaton --
                    (foldr (\x b -> N.addState b x)
                          N.empty
                          (statesAsInts))
                    -- end adding the states to the empty automaton --
                    (filter isInitialState statesAsInts))
              -- 2. adding the initial states --
              (filter isFinallState statesAsInts))
        -- 3. adding the final states --
        (filter (\x -> isTransition (fst $ fst x) (snd x) (snd $ fst x)) intTrans)
  -- 4. finally adding the transitions --
  where nbaStates = [(q, k') | q <- gnbaStates, k' <- [1..k]]
        nbaInitialStates = [(q, 1) | q <- gnbaInitialStates]
        nbaFinalStates = [(q, 1) | q <- gnbaFirstSet]
        gnbaStates = G.states g
        gnbaInitialStates = G.inicialStates g
        gnbafinalSets = G.finalSets g
        statesAsInts = M.keys stateMap
        gnbaFirstSet = if null gnbafinalSets then [] else head gnbafinalSets
        k = length gnbafinalSets
        -- now we need to store the representation of the sets --
        stateMap = M.fromList (zip [1..] nbaStates)
        -- now we make a list with all the possible transitions --
        possibleTransitions = [((s, s'), sigma) | s <- nbaStates,
                                                  s' <- nbaStates,
                                                  sigma <- alphabet,
                                                  isTransitionAllowed s sigma s']
        isTransitionAllowed s sigma s' =
          if fst s `notElem` gnbafinalSets!!(snd s - 1)
          then (sigma, fst s') `elem` (G.getNeighbours g (fst s))
               && snd s == snd s'
          else (sigma, fst s') `elem` (G.getNeighbours g (fst s))
               && snd s' == successor (snd s)
        successor i = if i < k then i + 1 else 1
        isInitialState x =  (stateMap M.! x) `elem` nbaInitialStates
        isFinallState x = (stateMap M.! x) `elem` nbaFinalStates
        isTransition s a s' = ((stateMap M.! s, stateMap M.! s'), a)
                              `elem` possibleTransitions
        intTrans = [((s, s'), sigma) | s <- statesAsInts,
                                       s' <- statesAsInts,
                                       sigma <- alphabet]

-- -----------------------------------------------------------------------------
-- END: Converting the GNBA to the NBA used in model checking
-- -----------------------------------------------------------------------------



-- -----------------------------------------------------------------------------
-- BEGIN: Making the automaton for the complementary language
-- -----------------------------------------------------------------------------

-- | Input: A Formula, number of agents, the list of actions available to the agent
--   Output: An GNBA that accepts the complementary language
--   NOTE: We assume that the agents start in 1..n. Must always
--         account for this when accessing states in the automaton.
--   NOTE: The numbers in the formulas must be consistent with the number of
--         agents provided. Otherwise this will not work
makeComplementaryGNBA :: F.GlobalFormula ->
                         Int ->          -- number of agents
                         [[Action]] ->        -- list with the actions
                         G.GNBA GNBAState AlphabetSymbol
makeComplementaryGNBA alpha n acts =
  -- finally we add the final sets
  foldr (\a b -> G.addFinalSet b a)
        -- third we add the transitions --
        (foldr (\a b -> G.addTransition b (fst $ fst a) (snd a) (snd $ fst a))
              -- second the initial states--
              (foldr (\a b -> G.addToInitialStates b a)
                    -- first we add the states --
                    (foldr (\a b -> G.addState b a) G.empty statesGNBA)
                    -- first we add the states --
                    initialStates)
              -- second the initial states --
              (filter (\a -> canBeGlobalAutomatonTransition alpha clo acts props (fst $ fst a) (snd $ fst a) (snd a))
                        possibleTransitions))
        -- third we add the transition
        finalSets
  -- finally we add the final sets
  where statesGNBA = makeStatesGNBA alpha n clo
        props = map ((S.filter F.isPropSymbol) . S.fromList . (F.subFormulasAgent alpha)) [1..n]
        clo = F.closureFormula alpha n
        initialStates = filter canBeInitialState statesGNBA
        possibleTransitions = makeMaybeTransitions statesGNBA acts
        finalSets = makeFinalSets statesGNBA alpha clo n


-- | Input: The states in the automaton, the global formula, the closure of the
--          the global formula, the number of agents
--   Output: The final sets of the automaton
makeFinalSets :: [GNBAState] -> -- all the states
                 F.GlobalFormula -> -- the formula
                 I.SOF -> -- the closure of the formula
                 Int -> -- the number of agents
                 [[GNBAState]]
makeFinalSets sts alpha clo n =
  [makerFormula f i | f <- globalFromulas, i <- agents] ++
  -- now we join the states witnessed by upsilon
  [[s | s <- sts, conditionUpsilon s]]
  where globalFromulas = S.toList $ S.filter F.isGlobally clo
        agents = [1..n]
        alpha' = F.wrapGlobal alpha
        -- makerFormula :: formula -> [GNBAStates]
        -- devolve os estados de todos os agentes para uma formula
        makerFormula f i = [s | s <- sts, conditionFormulaHolds f s i]
        conditionFormulaHolds f s i = f `S.member` (fst $ s!!(i-1))
                                      || (F.tailFormula f `S.notMember` (fst $ s!!(i-1)))
        -- because all the sets have the same global formulas and the same mark we can see
        -- if a set is in the upsilon accepting state just by testing the local state
        conditionUpsilon s = snd (head s) == Upsilon || alpha' `S.notMember` fst (head s)

-- | Input: The states in the automaton, a list with propSymbols for the agents
--          a list with all the actions
--   Output: A list with all the combinations of ((state, state), propSymbol)
--           regardless of that being a possible transition unde the automaton
--           rules or not.
makeMaybeTransitions :: [GNBAState] -> -- all the states in the automaton
                        --[I.SOF] -> -- the list with all the prop symbols
                        [[Action]] ->
                        [((GNBAState, GNBAState), AlphabetSymbol)]
makeMaybeTransitions states acts =
  [((s1, s2), symb) | s1 <- states, s2 <- states, symb <- mkSymb s1]
  where mkSymb s = [(foldr (\a b -> b `S.union` (S.filter F.isPropSymbol a))
                           S.empty
                           (map fst s), act) | act <- allActions]
        allActions = foldr (\a b -> b `union` a) [] acts


-- | Input: a global formula, the closure, a list with actions , a list
--          with the propositional symbols for the agents, two states and
--          a propositional letter
--   Output: True if it is a transition in the local automaton
--   NOTE: Possible optimization: use only the propositional symbols present in
--         the closure of the formula instead of all the propositional symbols.
canBeGlobalAutomatonTransition :: F.GlobalFormula ->
                                  I.SOF -> -- the closure
                                  [[Action]] -> -- actions of the agents
                                  [I.SOF] -> -- the prop symbols for the agents
                                  GNBAState -> -- state 1
                                  GNBAState -> -- state 2
                                  AlphabetSymbol -> -- letter responsible for the transition
                                  Bool
canBeGlobalAutomatonTransition alpha clo acts props s1 s2 sigma =
  -- first we check that all the states have coherent propositonal symbols --
  -- Check to see if i can just reduce this to s simple filter
  -- and then a check if sigma == filter isLiteral state
  all (\q -> (fst q) `S.intersection` (snd q) == propLetter `S.intersection` (snd q))
      (zip departureSets props) &&
  --all (\q -> S.filter F.isPropSymbol (fst q) == propLetter) s1 &&
  -- If it is not an action of agent i then the states must remain unchanged --
  all (\i -> S.filter F.isLocal (fst $ s1!!(i - 1)) ==
             S.filter F.isLocal (fst $ s2!!(i - 1)))
      sleppyAgents &&
  -- If it is an action of the agent then the rules for the local transition --
  -- function must hold --
  all (canBeLocalAutomatonTransition alpha clo s1 s2) activatedAgents &&
  -- Now we express the first rule for the communication formulas --
  all (\i -> all (\f -> F.tailFormula f `S.member` (arrivalSets!!(F.communicationAgent f - 1))
                        && F.communicationAgent f `elem` activatedAgents)
                 (S.filter F.isCommunication (arrivalSets!!(i - 1)))
      )
      activatedAgents &&
  -- Finally second communication rule --
  all (\i -> all (\f -> not (F.communicationAgent f `elem` activatedAgents
                         && F.tailFormula f `S.member` (arrivalSets!!(F.communicationAgent f - 1)))
                        || (f `S.member` (arrivalSets!!(i - 1)))
                 )
                 (filter F.isCommunication (F.subFormulasAgent alpha i))
      )
      activatedAgents
  where --atomicPropositions = map
        --literals = map (\x -> x `S.union` (S.map F.negateFormula x)) props
        departureSets = map fst s1
        arrivalSets = map fst s2
        propLetter = fst sigma
        action = snd sigma
        n = length s1 -- number of agents corresponds to the length of each state
        activatedAgents = filter (\i -> action `elem` acts!!(i - 1)) [1..n]
        sleppyAgents = [1..n] \\ activatedAgents


-- | Input: A a global formula, the closure of the formula, two states,
--          and the agent for which we want to check.
--   Output: True iff s2 in delta(s1, symb) in the complementary LOCAL automaton
canBeLocalAutomatonTransition :: F.GlobalFormula -> -- the formula we want to model check
                                 I.SOF -> -- the closure of the formula
                                 GNBAState -> -- the departure state
                                 GNBAState -> -- the arrival state
                                 F.Agent -> -- the agent for which we want to check
                                 Bool
canBeLocalAutomatonTransition alpha clo s1 s2 i =
  -- for X\pi --
  verifiesNext pairedStateSets &&
  -- for G\psi --
  verifiesGlobally pairedStateSets &&
  -- for th Upsilon marker --
  verifiesUpsilon pairedStates
  where destinySet = fst (s2!!(i - 1))
        departureSet = fst (s1!!(i - 1))
        pairedStateSets = (departureSet, destinySet)
        pairedStates = (s1!!(i - 1), s2!!(i - 1))
        alpha' = F.wrapGlobal alpha -- just so we can be in the Formulas domain
        -- the next condition --
        verifiesNext (s, s') =
          all (\x -> (x `S.notMember` s || F.tailFormula x `S.member` s') &&
                     (F.tailFormula x `S.notMember` s' || x `S.member` s)
              )
              (S.filter F.isNext clo)
        -- the global condition --
        verifiesGlobally (s, s') =
          all (\x -> (x `S.notMember` s || (F.tailFormula x `S.member` s && x `S.member` s')) &&
                     (not (F.tailFormula x `S.member` s && x `S.member` s') || x `S.member` s)
              )
              (S.filter F.isGlobally clo)
        -- the upsilon condition --
        verifiesUpsilon (s, s') = (not (snd s == Upsilon) || (alpha' `S.member` fst s && snd s' == Upsilon)) &&
                                  (not (alpha' `S.member` fst s && snd s' == Upsilon) || snd s == Upsilon)

-- | Input: A state of the GNBA
--   Output: True iff that state can be an initial state
canBeInitialState :: GNBAState -> Bool
canBeInitialState state =
  all (\x -> (not (I.hasCommunicationFormulas (fst x))) && (snd x /= Upsilon) ) state


-- | Input: A formula, The number of agents, the closure of the
--          formula, the propositional letter
--   Output: A list with the states for the GNBA, i.e, A list of lists [[(I.SOF, Marker)]]
makeStatesGNBA :: F.GlobalFormula -> -- the formula
                  Int -> -- the number of agents
                  I.SOF -> -- the closure
                  [GNBAState]
makeStatesGNBA alpha n clo =
  foldr (\a b -> [b' ++ [a'] | a' <- a, b' <- b,
                               I.haveSameGlobalFormulas (fst a') (fst $ head b'),
                               (snd $ head b') == snd a'])
        (map (\x -> [x]) (head iElemSets))
        (tail iElemSets)
  where iElemSets = map (\x -> concatMap (\y -> if F.wrapGlobal alpha `S.member` y
                                                then [(y, Upsilon), (y, None)]
                                                else [(y, None)])
                                         (I.iElementarySetsAgent clo x alpha)
                        )
                        [1..n]
-- -----------------------------------------------------------------------------
-- END: Making the automaton for the complementary language
-- -----------------------------------------------------------------------------


-- | Input: A DTS and, automaton and the closure of a formula.
--   Output: The product as defined in my thesis for the optimized automatons.
--   NOTE: The returned transition has a different labeling function.
--         This new transition system uses the state of the automaton
--         in the label of the local states.
--   NOTE: The states also change because they are the dot product.
dotProductParticullarCase :: (Ord s , Ord i, Ord a) =>
              T.DTS s i F.Formula a ->
              N.NBA (S.Set F.Formula, a) ->
              S.Set F.Formula ->
              T.DTS (s, N.State) i N.State a
dotProductParticullarCase dts auto clo =
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
                                     [(s, q) |s <- initialStatesT, q <- initialStatesN]
        -- adding the propositional symbols --
        dtsWithLabels = foldr (\x y -> foldr (\ag y' -> T.addStateLabel y' x ag [snd x])
                                             y
                                             agents)
                              dtsWithInitialStates
                              newStates
        -- adding to the transition relation -- 
        props = S.filter F.isPropSymbol clo
        dtsWithTransitions = foldr (\x y -> T.addTransition y (fst $ fst x) (snd $ fst x) (snd x))
                                   dtsWithLabels
                                   (makeTransitionStateDotProduct dts auto allActions props newStates)


-- | Input: An DTS, an NBA, a state of their product
--   Output: A list with tupples ((s, s'), a) denoting all the possible
--           transitions in DTS * NBA
makeTransitionStateDotProduct :: (Ord s, Ord i, Ord a) =>
                                 T.DTS s i F.Formula a ->
                                 N.NBA (S.Set F.Formula, a) ->
                                 [a] ->
                                 S.Set F.Formula ->
                                 [(s, N.State)] -> -- transition system states
                                 [(((s, N.State), (s, N.State)), a)]
makeTransitionStateDotProduct dts auto actions props states =
  foldr (\x@(s, q) y -> y ++
                        [((x, (s', q')), a) | a  <- actions,
                                              s' <- T.getNeighboursByAction dts s a,
                                              q' <- N.getNeighboursGeneral auto
                                                                           [q]
                                                                           (S.filter (`S.member` props) (S.fromList $ T.getLabel dts s), a)]
         )
        []
        states


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
                                     [(s, q) |s <- initialStatesT, q <- initialStatesN]
        -- adding the propositional symbols --
        dtsWithLabels = foldr (\x y -> foldr (\ag y' -> T.addStateLabel y' x ag [snd x])
                                             y
                                             agents)
                              dtsWithInitialStates
                              newStates
        -- adding to the transition relation --
        dtsWithTransitions = foldr (\x y -> T.addTransition y (fst $ fst x) (snd $ fst x) (snd x))
                                   dtsWithLabels
                                   [((s, s'), a) | s <- newStates,
                                                   s' <- newStates,
                                                   a <- allActions,
                                                   transitionIsPossible s s' a]
        transitionIsPossible s s' a =  ((snd s')
                                       `elem`
                                       (N.getNeighboursGeneral auto
                                                               [(snd s)]
                                                               (S.fromList $ T.getLabel dts (fst s), a)))
                                      &&
                                      (T.isTransitionOfSystem dts (fst s) (fst s') a)


-- just some test instances --
-- t = T.DTS {T.states = S.fromList [1, 2, 3, 4],
--          T.actions = M.fromList [(1, S.fromList ["a", "b"]), (2, S.fromList ["a", "c"])],
--          T.initialStates = S.fromList [1, 4],
--         T.propSymbols = M.fromList [
--             (1, S.fromList ["p1", "q1"]),
--             (2, S.fromList ["p2", "q2'"])
--                     ],
--         T.labelingFunction = M.fromList [
--                                       ((1, 1), S.fromList ["p"]),
--                                       ((1, 2), S.fromList ["q"]),
--                                       ((2, 1), S.fromList ["p"]),
--                                       ((2, 2), S.fromList []),
--                                       ((3, 1), S.fromList []),
--                                       ((3, 2), S.fromList ["q"]),
--                                       ((4, 1), S.fromList []),
--                                       ((4, 2), S.fromList [])
--                                       ],
--         T.transitionRelation = M.fromList [((3, "a"), [4]), ((4, "a"), [1])]}

-- g = N.NBA { N.states = [1, 2, 3],
--             N.finalStates = [1],
--             N.inicialStates = [1, 2],
--             N.delta = M.fromList [(1, [((S.fromList ["p"],"a"), 1), ((S.fromList ["q"],"b"), 2), ((S.fromList ["p"], "a"), 3)]) , (2, [((S.fromList ["p", "q"], "c"),3), ((S.fromList ["p", "q"],"a"), 1), ((S.fromList [],"a"), 3)]), (3, [(((S.fromList ["p", "q"],"c")), 3)])]
--         }

-- some test formulas
-- psiTeseLocal1 = F.Not ((F.Globally (F.PropositionalSymbol "p")))
-- psiTeseLocal2 = F.Not (F.Next (F.PropositionalSymbol "q"))
-- psiTeseGlobal = F.GImplies (F.Local 1 psiTeseLocal1) (F.Local 2 psiTeseLocal2)
-- testPsiTestAutomaton = makeComplementaryGNBA psiTeseGlobal
--                                              2
--                                              [["a", "b"], ["a", "c"]]
--                                              [S.fromList [F.FromLocal $ F.PropositionalSymbol "p"],
--                                               S.fromList [F.FromLocal $F.PropositionalSymbol "q"]]


-- -- smaller automatons for easy testing --
-- psiSmall = F.Next (F.PropositionalSymbol "p")
-- psiSmallGlobal = F.Local 1 psiSmall
-- psiSmallAuto = makeComplementaryGNBA psiSmallGlobal 1 [["a"]] [S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]]

-- psiSmall2 = F.Globally (F.PropositionalSymbol "p")
-- psiSmallGlobal2 = F.Local 1 psiSmall2
-- psiSmallAuto2 = makeComplementaryGNBA psiSmallGlobal2 1 [["a"]] [S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]]

-- psiSmall3 = F.Comunicates 1 (F.PropositionalSymbol "p")
-- psiSmallGlobal3 = F.Local 2 psiSmall3
-- psiSmallAuto3 = makeComplementaryGNBA psiSmallGlobal3 2 [["a", "b"], ["b"]] [S.fromList [F.FromLocal $ F.PropositionalSymbol "p"], S.fromList [F.FromLocal $ F.PropositionalSymbol "q"]]


-- psiSmall4 = (F.Local 1 (F.Not(F.Globally(F.Not $ F.PropositionalSymbol "p"))))
-- psiSmallAuto4 = makeComplementaryGNBA psiSmall4 1 [["a"]] [S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]]

-- -- A witness for "@_2[]c_1(p)"
-- tThesisComHolds = T.DTS {T.states = S.fromList [1, 2] :: S.Set Int,
--         T.actions = M.fromList [(1::Int, S.fromList ["a", "b"]), (2, S.fromList ["b"])],
--         T.initialStates = S.fromList [1],
--         T.propSymbols = M.fromList [
--             (1, S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
--             (2, S.fromList [F.FromLocal $ F.PropositionalSymbol "q"])
--                     ],
--         T.labelingFunction = M.fromList [
--                                       ((1, 1), S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
--                                       ((1, 2), S.fromList [F.FromLocal $ F.PropositionalSymbol "q"]),
--                                       ((2, 1), S.fromList []),
--                                       ((2, 2), S.fromList [])
--                                       ],
--         T.transitionRelation = M.fromList [
--                                           ((1, "a"), [2]),
--                                           ((2, "b"), [1])]}


-- -- a test instance for the convertions of GNBAs to NBAs
-- auto = G.GNBA {
--               G.states = [1, 2, 3, 4, 5]::[Int],
--               G.inicialStates = [1, 2],
--               G.finalSets = [[2, 3], [4]],
--               G.delta = M.fromList [(1, [("", 2)]),
--                                   (2, [("", 3)]),
--                                   (3, [("", 1)]),
--                                   (4, [("a", 5)]),
--                                   (5, [("a", 4)])]}
-- -- testing the dot product

-- tThesis = T.DTS {T.states = S.fromList [1, 2, 3, 4] :: S.Set Int,
--         T.actions = M.fromList [(1::Int, S.fromList ["a", "b"]), (2, S.fromList ["a", "c"])],
--         T.initialStates = S.fromList [1, 4],
--         T.propSymbols = M.fromList [
--             (1, S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
--             (2, S.fromList [F.FromLocal $ F.PropositionalSymbol "q"])
--                     ],
--         T.labelingFunction = M.fromList [
--                                       ((1, 1), S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
--                                       ((1, 2), S.fromList [F.FromLocal $ F.PropositionalSymbol "q"]),
--                                       ((2, 1), S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
--                                       ((2, 2), S.fromList []),
--                                       ((3, 1), S.fromList []),
--                                       ((3, 2), S.fromList [F.FromLocal $ F.PropositionalSymbol "q"]),
--                                       ((4, 1), S.fromList []),
--                                       ((4, 2), S.fromList [])
--                                       ],
--         T.transitionRelation = M.fromList [
--                                           ((1, "a"), [2, 4]),
--                                           ((1, "b"), [3]),
--                                           ((2, "c"), [1]),
--                                           ((3, "b"), [1]),
--                                           ((4, "a"), [2])]}


-- oneAgent1 = T.DTS {T.states = S.fromList [1, 2] :: S.Set Int,
--                    T.initialStates = S.fromList [1] :: S.Set Int,
--                    T.actions = M.fromList [(1::Int, S.fromList ["a"])],
--                    T.propSymbols = M.fromList [
--                       (1, S.fromList [F.FromLocal $ F.PropositionalSymbol "p"])],
--                    T.labelingFunction = M.fromList[
--                       ((1, 1), S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
--                       ((2, 1), S.fromList [])],
--                    T.transitionRelation = M.fromList[
--                       ((1, "a"), [2]),
--                       ((2, "a"), [1])]}

-- -- A witness for @_1[p] => @_2[X(X p)]. This is achieved by removing the 4th
-- -- state from tThesis and removing p from the second state.
-- -- This test is failing for the formula @_1[p] => @_2[X(Xp)]
-- tThesisNextNext = T.DTS {T.states = S.fromList [1, 2, 3] :: S.Set Int,
--         T.actions = M.fromList [(1::Int, S.fromList ["a", "b"]), (2, S.fromList ["a", "c"])],
--         T.initialStates = S.fromList [1],
--         T.propSymbols = M.fromList [
--             (1, S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
--             (2, S.fromList [F.FromLocal $ F.PropositionalSymbol "q"])
--                     ],
--         T.labelingFunction = M.fromList [
--                                       ((1, 1), S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]),
--                                       ((1, 2), S.fromList [F.FromLocal $ F.PropositionalSymbol "q"]),
--                                       ((2, 1), S.fromList []),
--                                       ((2, 2), S.fromList []),
--                                       ((3, 1), S.fromList []),
--                                       ((3, 2), S.fromList [F.FromLocal $ F.PropositionalSymbol "q"])
--                                       ],
--         T.transitionRelation = M.fromList [
--                                           ((1, "a"), [2]),
--                                           ((1, "b"), [3]),
--                                           ((2, "c"), [1]),
--                                           ((3, "b"), [1])]}


-- t8States2Agenst1 = T.generateDTSFromStdGen 2
--                                            [
--                                              [F.FromLocal $ F.PropositionalSymbol "p1", F.FromLocal $ F.PropositionalSymbol "p2"],
--                                              [F.FromLocal $ F.PropositionalSymbol "q1"]
--                                            ]
--                                            [["a", "b"], ["a", "c"]]
--                                            (mkStdGen 1)
--                                            0.1
--                                            0.1
-- fEasy1 = F.Local 1 (F.Next $ F.PropositionalSymbol "p1") -- can also be used with just one agent
