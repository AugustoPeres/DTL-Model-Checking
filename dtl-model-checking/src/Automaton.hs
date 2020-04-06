module Automaton
    (
      verifiesImplication
    , verifiesNegation
    , makeGlobalGNBA
    , GNBA
    , State
    , states
    , delta
    , inicialStates
    , finalStates
    , AlphabetSymbol
    , alpha -- this shoud not be here, using just fot testing
    , alphac
    , alphacLarge
    ) where

import           CommonTypes
import           Data.List       (nub)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import qualified Data.Set        as Set
import           DTLFormula

-- TODO: Clean up the code. I want this module to be independent from the formulas
--       module. To do that I cannot use constructors in this part of the code.
--       More getters have to be defined
--
--      Possible Optimizations : -> Fazer com que o closure escolha apenas conjuntos
--                                  de um dado tamnho


-- This part is designeted to building the automatons for the formula
-- We use the same data types for both local automatons and global automatons
-- since the destiction between the two is not necessary

-- Restriction : No automatoun can have more than maxBound::Int states
type State = Int
type Action = String
type AlphabetSymbol = (Set.Set Formula, Action) -- here the formulas are propositional symbols or the negations

data GNBA = GNBA {states        :: [State],
                  inicialStates :: [State],
                  stateMap      :: Map.Map State [Set.Set Formula],
                  finalStates   :: [Set.Set State],
                  delta         :: Map.Map State [(AlphabetSymbol, State)],
                  actions       :: [[Action]] -- we must keep tract of the actions of each agent
                 } deriving(Show)

{-
================================================================================
        Functions for the global automaton
================================================================================
-}

makeGlobalGNBA :: GlobalFormula -> Int -> [[Action]] -> GNBA
makeGlobalGNBA a n act =
  GNBA { states = s,
         inicialStates = makeInitialStates sm s a,
         stateMap = sm,
         finalStates = makeAcceptingSetsG sm a n s,
         delta = makeDeltaG clo act sm a s,
         actions = act
       }
  where l = map (\x -> makeLocalGNBA a x n (act!!x)) [1..n]
        s = [1..(length stateSets)]
        sm = makeStateMapG s stateSets
        stateSets = makeStateSetsG l
        clo = closureFormula a n

-- | Makes the accepting sets for the generalized Buchi automaton
--   Using the condition that we check Ga in q or (a) not in q
--   for the local formulas of some given agent.
makeAcceptingSetsG :: Map.Map State [Set.Set Formula] -> -- ^ mapping from the states to the corresponding sets
                      GlobalFormula -> -- ^ Global Formula
                      Int -> -- ^ number of agents present in the global automatons
                      [State] -> -- ^ all the states in the automaton
                      [Set.Set State] -- ^ Return: a list with the accepting sets
makeAcceptingSetsG sm a n states =
  concat [helper agent | agent <- [1..n]]
  where helper :: Agent -> [Set.Set State]
        helper i = [makeSet f i| f <- filter isGlobally (subFormulasAgent a i)]
        makeSet :: Formula -> Agent -> Set.Set State
        makeSet f i' = Set.fromList $ filter (\x -> conditionHolds f ((fromJust $ Map.lookup x sm)!!(i'-1))) states
        conditionHolds :: Formula -> Set.Set Formula -> Bool
        conditionHolds f set = f `Set.member` set || tailFormula f `Set.notMember` set


-- | Receives a list of local Automatons and computes the
--   states on the Global automaton.
makeStateSetsG :: [GNBA] -> [[Set.Set Formula]]
makeStateSetsG automatons =
  helper (map getSetsGNBA automatons)
  where helper (x:[rest]) = [a ++ b | a <- x, b <- rest, haveSameGlobalFormulas a b]
        helper (x:xs)     = [a ++ b | a <- x, b <- helper xs, haveSameGlobalFormulas a b]

-- | Receives a list of states(Int) and a list of [Sets]
--   representing the states in the global automaton
--   Returns: A mapping from integers to sets {1: [{}{}], 2:[{}{}]...}
makeStateMapG :: [State] -> [[Set.Set Formula]] -> Map.Map State [Set.Set Formula]
makeStateMapG s s' = Map.fromList $ zip s s'

-- | Makes the transition function for the global automaton
makeDeltaG :: Set.Set Formula -> -- ^ closure of the formula
              [[Action]] -> -- ^ actions for each agent
              Map.Map State [Set.Set Formula] -> -- ^ mapping from States to the corresponding sets
              GlobalFormula -> -- ^ formula for which the automaton is being made
              [State] -> -- ^ states in the automaton represented as integers
              Map.Map State [(AlphabetSymbol, State)] -- ^ returns the transition function as a Map
makeDeltaG clo act' sm a s =
  Map.fromList [(state, [(symbol, state') | symbol <- possibleSymbols, state' <- s, condition state state' symbol]) | state <- s]
  where possibleSymbols = [(val, a) | val <- valuations, a <- act]
        valuations = Set.toList $ Set.powerSet psymbs
        act = nub $ concat act'
        psymbs = Set.filter isPropSymbol clo
        condition x y z = isTransitionAllowedG x y z clo act' sm a

-- | Checks if a transition is possible from one state to
--   to the other given some alphabet symbol.
isTransitionAllowedG :: State -> -- ^ original state
                        State -> -- ^ goal state
                        AlphabetSymbol -> -- ^ alphabet symbol
                        Set.Set Formula -> -- ^ closure of the formula
                        [[Action]] -> -- ^ actions off all the agents
                        Map.Map State [Set.Set Formula] -> -- ^ mapping to the sets representing the states
                        GlobalFormula -> -- ^ we need the global formula to obtain the sub formulas of an agent
                        Bool -- ^ True iff the transition is possible
isTransitionAllowedG o g sigma clo act sm a =
  all (\x -> isActionOfAgent action x act || ((origin!!(x-1) == goal!!(x-1)) && localVal!!(x-1)==(Set.filter isPropSymbol (origin!!(x-1))))) agents && -- if it is not action it must remain unchanged
  all (\x -> all (\y -> not (isActionOfAgent action x act) || Set.member (tailFormula y) (goal!!((communicationAgent y) - 1)))(Set.filter isCommunication (goal!!(x - 1)))) agents &&
  all checkCondition agents &&
  all (\x -> not (isActionOfAgent action x act)|| isTransitionAllowed o sm clo (x-1) g && Set.filter isPropSymbol (origin!!(x-1)) == localVal!!(x-1)) agents
  where origin = fromJust $ Map.lookup o sm -- [Set1, Set2, Set3]
        goal   = fromJust $ Map.lookup g sm -- [Set1', Set2', Set3']
        agents = [1..(length origin)] --list with all the agents
        localVal = map (\x -> downArrow valuation x a) agents
        valuation = fst sigma
        action = snd sigma
        --sm = stateMap auto -- maping to the states
        lits = map literals origin --list with all literals in each set od the state
        checkCondition x = all (\f -> (all (\j -> Set.member f (goal!!(x - 1)) || not(isActionOfAgent action j act && Set.member (tailFormula f) (goal!!(j - 1)) )) agents)) (filter isCommunication (subFormulasAgent a x))

-- | Receives an action and, an agent and decides if the action
--   is an action of said agent
isActionOfAgent :: Action -> Agent -> [[Action]] -> Bool
isActionOfAgent a i act' =
  a `elem` act
  where act = act' !! (i - 1)

{-
================================================================================
        End of the functions for the global automaton
================================================================================
-}


{-
================================================================================
      This functions are only for the local GNBA
================================================================================
-}

-- | Returns all the sets in the automaton [[Set1, Set2], [S, S'],...]
getSetsGNBA :: GNBA -> [[Set.Set Formula]]
getSetsGNBA g =
  [fromJust $ Map.lookup k sm | k <- s]
  where sm = stateMap g
        s  = states g

-- Construction of the automaton

makeLocalGNBA :: GlobalFormula -> -- formula for which the automaton is made
                 Agent -> -- agent for which we make the automaton
                 Int -> -- number of agents
                 [Action] -> -- actions of the agent
                 GNBA
makeLocalGNBA a i n act =
  GNBA {
        states = s,
        inicialStates = makeInitialStates sm s a,
        stateMap = sm,
        finalStates = makeAcceptingSets clo sm s,
        delta = makeDelta s sm clo lit act,
        actions = [act]
       }
  where clo = closureFormula a n
        s = [1..(length necessarySets)]
        sm = makeStateMap s necessarySets
        lit = Set.union propSymbs (Set.map negateFormula propSymbs)
        --
        necessarySets = filter (FromGlobal a `Set.member` ) (iElementarySets a i n propSymbs)
        propSymbs = Set.fromList $ filter isPropSymbol subForms
        subForms = subFormulasAgent a i

makeDelta :: [State] -> -- states in the automaton
             Map.Map State [Set.Set Formula] -> -- keep track of the states
             Set.Set Formula -> -- closure of the formual
             Set.Set Formula -> -- propositional symbols and the negations (Lit_i)
             [Action] -> -- actions for the agent
             Map.Map State [(AlphabetSymbol, State)]
makeDelta s ms clo lit act =
  foldl (addStateImages ms lit act s clo) delta s
  where delta = Map.fromList (zip s (take (length s) (repeat [])))

-- add to the Map the transitions for a given state
addStateImages :: Map.Map State [Set.Set Formula] -> -- map with all the states
                  Set.Set Formula -> -- Lit_i
                  [Action] -> -- list of actions
                  [State] -> -- all the states
                  Set.Set Formula -> -- closure of the formula
                  Map.Map State [(AlphabetSymbol, State)] -> -- map used in the fold
                  State ->
                  Map.Map State [(AlphabetSymbol, State)]
addStateImages ms lit act states clo rmap s =
  Map.insertWith (++) s (transitionsState ms lit s states act clo) rmap

-- all the possible transitions fot a given state
transitionsState :: Map.Map State [Set.Set Formula] -> -- all the states
                    Set.Set Formula -> --literals
                    State -> --State
                    [State] -> -- all the states
                    [Action] ->
                    Set.Set Formula -> -- closure of the formula
                    [(AlphabetSymbol, State)]
transitionsState ms li s states act clo =
  [(symbol, state) | symbol <- possibleSymbols, state <- pS]
  where possibleSymbols = [(literals state , a) | a <- act]
        pS = possibleStates s ms states clo
        state = head $ fromJust (Map.lookup s ms)

-- Returns all the states from one state
possibleStates :: State -> Map.Map State [Set.Set Formula] -> [State] -> Set.Set Formula -> [State]
possibleStates s ms states clo = filter (isTransitionAllowed s ms clo 0) states

-- | Checks if a transition is possible from one state to the other
--   at some level.
--   Example: s1 = [Set1, Set2, Set3]; s2 = [Set1', Set2', Set3']
--            When checking at level 1 returns True iff the transition
--            Set2 -> Set2' is allowd
isTransitionAllowed :: State -> -- ^ departure state
                       Map.Map State [Set.Set Formula] -> -- ^ track the states
                       Set.Set Formula -> -- ^ closure. Necessary for one side of the implication
                       Int -> -- ^ Checks for any given set in the state. In the case og local automatons should always be 0
                       State -> -- ^ destination state
                       Bool     -- True iff the transition is allowed
isTransitionAllowed s ms clo level d =
  -- Implication on the left
  (all (\x -> x `Set.member` origin || tailFormula x `Set.notMember` destiny) nextFormulasclo &&
  all (\x -> x `Set.member` origin || not (x `Set.member`destiny && tailFormula x `Set.member` origin)) globalFormulasclo)
   &&
   -- Implication on the right
  (all (\x -> tailFormula x `Set.member` destiny) nextFormulas &&
  all (\x -> tailFormula x `Set.member` origin && x `Set.member`destiny) globalFormulas)
  where origin            = (fromJust (Map.lookup s ms))!!level
        destiny           = (fromJust (Map.lookup d ms))!!level -- raises an error when not present
        nextFormulas      = Set.filter isNext origin
        globalFormulas    = Set.filter isGlobally origin
        nextFormulasclo   = Set.filter isNext clo
        globalFormulasclo = Set.filter isGlobally clo

makeStateMap :: [State] -> [Set.Set Formula] -> Map.Map State [Set.Set Formula]
-- We should be careful here as diferent sizes in one of the list will
-- make us lose information
makeStateMap s s' = Map.fromList (zip s (map aux s'))
                    where aux x = [x]

makeInitialStates :: Map.Map State [Set.Set Formula] -> -- the map to the states
                     [State] -> -- all the states in the automaton
                     GlobalFormula -> -- we must ensure the formula is in the inicial state
                     [State]
makeInitialStates sm s a =
  filter faux s
  where faux x = all (\q -> noCom q && (FromGlobal a) `Set.member` q) (fromJust $ Map.lookup x sm)
        noCom = not . hasCommunicationFormulas
        -- this throws an error if a key is not found

makeAcceptingSets :: Set.Set Formula -> -- Closure of the formula
                     Map.Map State [Set.Set Formula] -> -- map to the states
                     [State] -> -- states in the automaton
                     [Set.Set State]
makeAcceptingSets clo ms s =
  map helper (Set.toList $ Set.filter isGlobally clo)
  where helper :: Formula -> Set.Set State
        helper f =
          Set.fromList $ filter ((\x -> Set.member f x || not (Set.member (tailFormula f) x)) . head . fromJust . (\x -> Map.lookup x ms)) s
          -- this throws an error if the key is not found


{-|
  This final function just converts the automaton to graphviz
  to make debuging possible errors  easier
-}
gnbaToGraphviz :: GNBA -> String
gnbaToGraphviz gnba =
  concatMap (transToString gnba) (states gnba)

transToString :: GNBA -> State -> String
transToString gnba k =
  foldl (\y x -> show k ++ "->" ++ show(arrival x) ++ "[label=\"" ++ symbShow x ++ "\"];\n" ++ y) "" aux
  --foldl (\y x -> show k ++ "->" ++ show(arrival x) ++ ";\n" ++ y) "" aux
  where arrival (a, b) = b
        aux = fromJust $ Map.lookup k (delta gnba)
        symbShow ((set, action), b) = "<" ++ Set.foldl (\x y -> x ++ y ++ ",") "" (Set.map show set) ++ action ++ ">"

{-
================================================================================
      End of functions for the local GNBA
================================================================================
-}

-- This parts is used to check if a set is i-elementary
-- and performs other operatios on sets

-- Returns a set with only propositional symbols and negations
literals :: Set.Set Formula -> Set.Set Formula
literals = Set.filter isLiteral

--returns True if the set has a formula of type Gpsi
hasG :: Set.Set Formula -> Bool
hasG s = Set.null $ Set.filter isGlobally s

--returns True if the set has a formula of type Xpsi
hasX :: Set.Set Formula -> Bool
hasX s = Set.null $ Set.filter isNext s

hasCommunicationFormulas :: Set.Set Formula -> Bool
hasCommunicationFormulas s =  any (isCommunication) s -- can be improved with any

iElementarySets :: GlobalFormula -> -- formula used for the closure
                   Agent ->
                   Int -> -- number of agents
                   Set.Set Formula -> -- porpositional symbols of the agent
                   [Set.Set Formula]
iElementarySets a i n lit =
  nub [downArrow c i a | c <- Set.toList auxset,
                         isIElementary c i a n]
  where auxset = Set.powerSet (Set.union clo lit)
        clo = closureFormula a n

{-|
  Implements the down arrow function as describes int the thesis
-}
downArrow :: Set.Set Formula -> Agent -> GlobalFormula -> Set.Set Formula
downArrow b i a = Set.filter (\x -> x `Set.member` aux || (isGlobal x) ) b
                  where formulasAgent = Set.fromList $ subFormulasAgent a i
                        aux           = Set.union aux2 aux3
                        aux2          = Set.map negateFormula aux3
                        aux3          = Set.fromList $ subFormulasAgent a i

{-|
  Checks if a set is i-elementary
-}
isIElementary :: Set.Set Formula ->
                 Agent -> -- agent for wich we check
                 GlobalFormula ->
                 Int -> -- number of agents
                 Bool
isIElementary b i a n = if not (Set.null b)
                           then verifiesGlobally b &&
                                verifiesNegation b &&
                                verifiesImplication b a  n &&
                                verifiesIConsistent b i a n &&
                                verifiesMaximal b n a
                           else False

{-|
  Checks if the condition f1 => f1 iff ~f1 in B or f2 in B for all
  the implications in the closure of a hold
-}
verifiesImplication :: Set.Set Formula -> GlobalFormula -> Int -> Bool
verifiesImplication b a n =
  all (helper b) implications
  where implications = Set.filter isImplication clo
        clo = closureFormula a n
        helper set f = if Set.member f set
                          then aux
                          else not aux
                       where aux = Set.member f2 set ||
                                   Set.member (negateFormula f1) set
                             f1 = head subF
                             f2 = subF!!1
                             subF = getSubFormulasImplication f

{-|
  Checks if the condition psi in B => ~psi not in B
-}
verifiesNegation :: Set.Set Formula -> Bool
verifiesNegation set =
  all (helper set) set
  where helper b f = not (Set.member f b) || not (Set.member (negateFormula f) b)

{-|
  Checks if the condition Gpsi in B => psi in B
-}
verifiesGlobally :: Set.Set Formula -> Bool
verifiesGlobally set =
  all (helper set) set
  where helper b f = not (isGlobally f) || tailFormula f `Set.member` b

{-|
  This set verifies if the condition
       @_i[y] in B iff y in B
  holds for agent i
-}
verifiesIConsistent :: Set.Set Formula -> Agent -> GlobalFormula -> Int -> Bool
verifiesIConsistent b i a n =
  all (helper b) l
  where l = Set.filter ( `isAtAgent` i ) clo
        clo = closureFormula a n
        helper set f = (not (tailFormula f `Set.member` set) || f `Set.member` set) &&
                       (not (f `Set.member` set) || tailFormula f `Set.member` set)

{-| Checks if a set is maximal-}
verifiesMaximal :: Set.Set Formula ->
                   Int -> -- number of agents
                   GlobalFormula -> -- Formula used for the closure
                   Bool
verifiesMaximal b n a =
  --Set.findMin $ Set.map (helper b) clo
   all (helper b) clo
  where clo = closureFormula a n
        helper set f = (Set.member f set) || Set.member (negateFormula f) set

haveSameGlobalFormulas :: [Set.Set Formula] -> [Set.Set Formula] -> Bool
haveSameGlobalFormulas s1 s2 =
  allEqual l
  where l = map (Set.filter isGlobal) s1 ++ map (Set.filter isGlobal) s2
        allEqual xs = and $ map (== head xs) (tail xs)

psiSetsL1 = PropositionalSymbol "p"
psiSetsL2 = PropositionalSymbol "q"
psiSetsL  = GImplies (Local 1 psiSetsL1) (Local 2 psiSetsL2)

f1 = Globally (PropositionalSymbol "p")
f2 = Globally (PropositionalSymbol "q")
alpha = GImplies (Local 1 f1) (Local 2 f2)

f1c = (Next (Comunicates 2 (PropositionalSymbol "p")))
alphac = Local 1 f1c

f1cLarge = (Next (Globally (Implies (PropositionalSymbol "p") (Comunicates 2 (PropositionalSymbol "q")))))
f2cLarge = (Next ( PropositionalSymbol "q"))
alphacLarge = GImplies (Local 1 f1cLarge) (Local 2 f2cLarge)

f1Benchmark = Next (Globally (Implies (PropositionalSymbol "p") (Comunicates 2 (PropositionalSymbol "q"))))
f2Benchmark = Implies (Next ( PropositionalSymbol "q")) (Implies (Next (PropositionalSymbol "q")) (PropositionalSymbol "q"))
alphaBenchmark = GImplies (Local 1 f1Benchmark) (Local 2 f2Benchmark)
