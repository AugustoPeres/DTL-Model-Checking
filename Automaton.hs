module Automaton
    (
      verifiesImplication
    , verifiesNegation
    ) where

import           Data.List       (nub)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import qualified Data.Set        as Set
import           DTLFormula

-- TODO: Clean up the code. I want this module to be independent from the formulas
--       module. To do that I cannot use constructors in this part of the code.
--       More getters have to be defined

-- This part is designeted to building the automatons for the formula
-- We use the same data types for both local automatons and global automatons
-- since the destiction between the two is not necessary

-- Restriction : No automatoun can have more than maxBound::Int states
type State          = Int
type Action         = String
type AlphabetSymbol = (Set.Set Formula, Action) -- here the formulas are propositional symbols or the negations

data GNBA = GNBA {states        :: [State],
                  inicialStates :: [State],
                  stateMap      :: Map.Map State [Set.Set Formula],
                  finalStates   :: [Set.Set State],
                  delta         :: Map.Map State [(AlphabetSymbol, State)],
                  actions       :: [Action] -- we must keep tract of the actions
                 } deriving(Show)

{-
================================================================================
      This functions are only for the local GNBA
================================================================================
-}

makeLocalGNBA :: GlobalFormula -> -- formula for which the automaton is made
                 Agent -> -- agent for which we make the automaton
                 Int -> -- number of agents
                 [Action] -> -- actions of the agent
                 GNBA
makeLocalGNBA a i n act =
  GNBA {
        states = s,
        inicialStates = makeInitialStates sm s,
        stateMap = sm,
        finalStates = makeAcceptingSets clo sm s,
        delta = makeDelta s sm clo lit act,
        actions = act
       }
  where clo = closureFormula a n
        s = [1..(length necessarySets)]
        sm = makeStateMap s necessarySets
        lit = Set.union propSymbs (Set.map negateFormula propSymbs)
        --
        necessarySets = iElementarySets a i n propSymbs
        propSymbs = Set.fromList $ filter isPropSymbol subForms
        subForms = (subFormulasAgent a i)

makeDelta :: [State] -> -- states in the automaton
             Map.Map State [Set.Set Formula] -> -- keep track of the states
             Set.Set Formula -> -- closure of the formual
             Set.Set Formula -> -- propositional symbols and the negations (Lit_i)
             [Action] -> -- actions for the agent
             Map.Map State [(AlphabetSymbol, State)]
makeDelta s ms clo lit act =
  foldl (addStateImages ms lit act s clo) delta s
  where delta = Map.fromList (zip s (take (length s) (repeat [])))


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

possibleStates :: State -> Map.Map State [Set.Set Formula] -> [State] -> Set.Set Formula -> [State]
possibleStates s ms states clo = filter (isTransitionAllowed s ms clo) states

isTransitionAllowed :: State -> -- departure state
                       Map.Map State [Set.Set Formula] -> -- track the states
                       Set.Set Formula -> -- closure. Necessary for one side of the implication
                       State -> -- destiny state
                       Bool     -- True iff the transition is allowed
isTransitionAllowed s ms clo d =
  -- Implication on the left
  (all (\x -> x `Set.member` origin || tailFormula x `Set.notMember` destiny) nextFormulasclo &&
  all (\x -> x `Set.member` origin || not (x `Set.member`destiny && tailFormula x `Set.member` origin)) globalFormulasclo)
   &&
   -- Implication on the right
  (all (\x -> tailFormula x `Set.member` destiny) nextFormulas &&
  all (\x -> tailFormula x `Set.member` origin && x `Set.member`destiny) globalFormulas)
  where origin            = head $ fromJust (Map.lookup s ms)
        destiny           = head $ fromJust (Map.lookup d ms) -- raises an error when not present
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
                     [State]
makeInitialStates ms s =
  filter faux s
  where faux x = not . hasCommunicationFormulas . head . fromJust $ Map.lookup x ms
        -- this throws an error if a key is not found

makeAcceptingSets :: Set.Set Formula -> -- Closure of the formula
                     Map.Map State [Set.Set Formula] -> -- map to the states
                     [State] -> -- states in the automaton
                     [Set.Set State]
makeAcceptingSets clo ms s =
  map helper (Set.toList $ Set.filter isGlobally clo)
  where helper :: Formula -> Set.Set State
        helper f@(FromLocal (Globally psi)) =
          Set.fromList $ filter ((\x -> Set.member f x || not (Set.member (FromLocal psi) x)) . head . fromJust . (\x -> Map.lookup x ms)) s
          -- this throws an error if the key is not found
        helper _ = undefined


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
hasCommunicationFormulas s =  Set.findMin $ Set.map (isCommunication) s

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
-- TODO: Make this function prettier with isImplication and the something lieke
--       getImplicationSubFormulas
verifiesImplication :: Set.Set Formula -> GlobalFormula -> Int -> Bool
verifiesImplication b a n =
  Set.findMin $ Set.map (helper b) implications
  where implications = Set.filter isImplication clo
        clo = closureFormula a n
        helper set f@(FromLocal (Implies f1 f2)) = if Set.member f set
                                                      then aux
                                                      else not aux
                                                    where aux = Set.member (FromLocal (Not f1)) set || Set.member (FromLocal f2) set
        helper set f@(FromGlobal (GImplies f1 f2)) = if Set.member f set
                                                      then aux
                                                      else not aux
                                                    where aux = Set.member (FromGlobal (GNot f1)) set || Set.member (FromGlobal f2) set
        helper _ _                                  = undefined

{-|
  Checks if the condition psi in B => ~psi not in B
-}
verifiesNegation :: Set.Set Formula -> Bool
verifiesNegation set =
  Set.findMin $ Set.map (helper set) set
  where helper b f = not (Set.member f b) || not (Set.member (negateFormula f) b)

{-|
  Checks if the condition Gpsi in B => psi in B
-}
verifiesGlobally :: Set.Set Formula -> Bool
verifiesGlobally set =
  Set.findMin $ Set.map (helper set) set
  where helper b (FromLocal (Globally f)) = Set.member (FromLocal f) b
        helper _ _                        = True

{-|
  This set verifies if the condition
       @_i[y] in B iff y in B
  holds for agent i
-}
verifiesIConsistent :: Set.Set Formula -> Agent -> GlobalFormula -> Int -> Bool
verifiesIConsistent b i a n =
  Set.findMin $ Set.map (helper b) l
  where l = Set.filter ( `isAtAgent` i ) clo
        clo = closureFormula a n
        helper set f@(FromGlobal (Local _ f2)) = if Set.member f set
                                                    then aux
                                                    else not aux
                                                 where aux = Set.member (FromLocal f2) set
        helper _ _                             = undefined

{-| Checks if a set is maximal-}
verifiesMaximal :: Set.Set Formula ->
                   Int -> -- number of agents
                   GlobalFormula -> -- Formula used for the closure
                   Bool
verifiesMaximal b n a =
  Set.findMin $ Set.map (helper b) clo
  where clo = closureFormula a n
        helper set f = (Set.member f set) || Set.member (negateFormula f) set

psiSetsL1 = PropositionalSymbol "p"
psiSetsL2 = PropositionalSymbol "q"
psiSetsL  = GImplies (Local 1 psiSetsL1) (Local 2 psiSetsL2)

f1 = Next (PropositionalSymbol "p")
f2 = Globally (PropositionalSymbol "q")
alpha = GImplies (Local 1 f1) (Local 2 f2)
