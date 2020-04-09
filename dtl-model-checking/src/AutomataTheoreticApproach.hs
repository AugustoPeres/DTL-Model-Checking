{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module AutomataTheoreticApproach (modelCheck)
  where


import           CommonTypes
import           Data.List     (union, (\\))
import qualified Data.Map.Lazy as M
import qualified Data.Set      as S
import qualified DTLFormula    as F
import qualified DTS           as T
import qualified GNBA          as G
import qualified NBA           as N
import qualified Ielementary as I

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

instance {-# OVERLAPPING #-} Show AlphabetSymbol where
  show sigma = "<" ++
               S.foldr (\a b -> b ++ show a ++ ",") "" (fst sigma) ++
               show (snd sigma) ++
               ">"
-- -----------------------------------------------------------------------------
-- END: Here we instance show for our types, this makes debuging much easir
-- -----------------------------------------------------------------------------



-- | Input: A transition system, a DTL formula and an integer.
--   Output: Yes iff the transition system satisfies the formula
--   This is the MAIN function on the module.
modelCheck :: (Ord s, Ord i, Ord prop, Ord a) =>
              T.DTS s i prop a ->
              F.GlobalFormula ->
              Int -> -- number of agents
              Bool
modelCheck t alpha n = undefined


-- -----------------------------------------------------------------------------
-- BEGIN: Making the automaton for the complementary language
-- -----------------------------------------------------------------------------

-- | Input: A Formula, number of agents, a list of action, a list
--          with all propositional symbols for the agents
--   Output: An GNBA that accepts the complementary language
--   NOTE: We assume that the agents start in 1..n. Must always
--         account for this when accessing states in the automaton.
--   NOTE: The numbers in the formulas must be consistent with the number of
--         agents provided. Otherwise this will not work
makeComplementaryGNBA :: F.GlobalFormula ->
                         Int ->          -- number of agents
                         [[Action]] ->        -- list with the actions
                         [I.SOF] -> -- propositional symbols for each agent
                         G.GNBA GNBAState AlphabetSymbol
makeComplementaryGNBA alpha n acts props=
  -- third we add the transitions --
  foldr (\a b -> G.addTransition b (fst $ fst a) (snd a) (snd $ fst a))
        -- second the initial states--
        (foldr (\a b -> G.addToInitialStates b a)
              -- first we add the states --
              (foldr (\a b -> G.addState b a) G.empty statesGNBA)
              -- first we add the states --
              initialStates)
        -- second the initial states --
        (filter (\a -> canBeGlobalAutomatonTransition alpha clo acts props (fst $ fst a) (snd $ fst a) (snd a))
                 possibleTransitions)
  -- third we add the transition
  where statesGNBA = makeStatesGNBA alpha n clo props
        clo = F.closureFormula alpha n
        initialStates = filter canBeInitialState statesGNBA
        possibleTransitions = makeMaybeTransitions statesGNBA props acts


-- | Input: The states in the automaton, a list with propSymbols for the agents
--          a list with all the actions
--   Output: A list with all the combinations of ((state, state), propSymbol)
--           regardless of that being a possible transition unde the automaton
--           rules or not.
makeMaybeTransitions :: [GNBAState] -> -- all the states in the automaton
                        [I.SOF] -> -- the list with all the prop symbols
                        [[Action]] ->
                        [((GNBAState, GNBAState), AlphabetSymbol)]
makeMaybeTransitions states propSymbols acts =
  [((s1, s2), symb) | s1 <- states, s2 <- states, symb <- mkSymb s1]
  where mkSymb s = [(foldr (\a b -> b `S.union` (S.filter F.isLiteral a))
                           S.empty
                           (map fst s), act) | act <- allActions]
        allActions = foldr (\a b -> b `union` a) [] acts


-- | Input: a global formula, the closure, a list with actions , a list
--          with the propositional symbols for the agents, two states and
--          a propositional letter
--   Output: True if it is a transition in the local automaton
canBeGlobalAutomatonTransition :: F.GlobalFormula ->
                                  I.SOF -> -- the closure
                                  [[Action]] -> -- actions of the agents
                                  [I.SOF] -> -- the prop symbols for the agents
                                  GNBAState -> -- state 1
                                  GNBAState -> -- state 2
                                  AlphabetSymbol -> -- letter responsible for the transition
                                  Bool
canBeGlobalAutomatonTransition alpha clo acts props s1 s2 sigma =
  -- first we check that all the states have coherent proposisitonal symbols --
  -- Check to see if i can just reduce this to s simple filter
  -- and then a check if sigma == filter isLiteral state
  all (\q -> (fst q) `S.intersection` (snd q) == propLetter `S.intersection` (snd q))
      (zip departureSets literals) &&
  -- If it is not an action of agent i then the states must remain unchanged --
  all (\i -> s1!!(i - 1) == s2!!(i - 1)) sleppyAgents &&
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
  all (\i -> all (\f -> not ((F.communicationAgent f `elem` activatedAgents
                         && F.tailFormula f `S.member` (arrivalSets!!(F.communicationAgent f - 1))))
                        || (f `S.member` (arrivalSets!!(i - 1)))
                 )
                 (filter F.isCommunication (F.subFormulasAgent alpha i))
      )
      activatedAgents
  where literals = map (\x -> x `S.union` (S.map F.negateFormula x)) props
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
        -- literals = map (\x -> x `S.union` (S.map F.negateFormula x)) props this goes to the global function
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
                  [I.SOF] -> -- a list with the propositional symbols of each agent
                  [GNBAState]
makeStatesGNBA alpha n clo props =
  foldr (\a b -> [b' ++ [a'] | a' <- a, b' <- b,
                               I.haveSameGlobalFormulas (fst a') (fst $ head b'),
                               (snd $ head b') == snd a'])
        (map (\x -> [x]) (head iElemSets))
        (tail iElemSets)
  where iElemSets = map (\x -> concatMap (\y -> if F.wrapGlobal alpha `S.member` y
                                                then [(y, Upsilon), (y, None)]
                                                else [(y, None)])
                                         (I.iElementarySetsAgent clo x (props!!(x-1)) alpha)
                        )
                        [1..n]
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

-- some test formulas
psiTeseLocal1 = F.Not ((F.Globally (F.PropositionalSymbol "p")))
psiTeseLocal2 = F.Not (F.Next (F.PropositionalSymbol "q"))
psiTeseGlobal = F.GImplies (F.Local 1 psiTeseLocal1) (F.Local 2 psiTeseLocal2)
testPsiTestAutomaton = makeComplementaryGNBA psiTeseGlobal
                                             2
                                             [["a", "b"], ["a", "c"]]
                                             [S.fromList [F.FromLocal $ F.PropositionalSymbol "p"],
                                              S.fromList [F.FromLocal $F.PropositionalSymbol "q"]]


-- smaller automatons for easy testing --
psiSmall = F.Next (F.PropositionalSymbol "p")
psiSmallGlobal = F.Local 1 psiSmall
psiSmallAuto = makeComplementaryGNBA psiSmallGlobal 1 [["a"]] [S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]]

psiSmall2 = F.Globally (F.PropositionalSymbol "p")
psiSmallGlobal2 = F.Local 1 psiSmall2
psiSmallAuto2 = makeComplementaryGNBA psiSmallGlobal2 1 [["a"]] [S.fromList [F.FromLocal $ F.PropositionalSymbol "p"]]

psiSmall3 = F.Comunicates 2 (F.PropositionalSymbol "q")
psiSmallGlobal3 = F.Local 1 psiSmall3
psiSmallAuto3 = makeComplementaryGNBA psiSmallGlobal3 2 [["a", "b"], ["a", "c"]] [S.fromList [F.FromLocal $ F.PropositionalSymbol "p"], S.fromList [F.FromLocal $ F.PropositionalSymbol "q"]]
