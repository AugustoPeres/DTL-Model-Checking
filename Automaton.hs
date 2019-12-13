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
-- This part is designeted to building the automatons for the formula
-- We use the same data types for both local automatons and global automatons
-- since the destiction between the two is not necessary

-- Restriction : No automatoun can have more than maxBound::Int states
type State          = Int
type Action         = String
type AlphabetSymbol = (Set.Set Formula, Action)

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
makeLocalGNBA a i n = undefined

makeDelta :: [State] -> -- states in the automaton
             Map.Map State [Set.Set Formula] -> -- keep track of the states
             Set.Set Formula -> -- propositional symbols
             [Action] -> -- actions for the agent
             Map.Map State [(AlphabetSymbol, State)]
makeDelta = undefined

makeStateMap :: [State] -> [Set.Set Formula] -> Map.Map State [Set.Set Formula]
-- We should be careful here as diferent sizes in one of the list will
-- make us lose information
makeStateMap s s' = Map.fromList (zip s (map aux s'))
                    where aux x = [x]

makeInitialStates :: Set.Set Formula -> -- Closure of the formula. To avoid a
                     -- repetitive call to the function
                     Map.Map State [Set.Set Formula] -> -- the map to the states
                     [State] -> -- all the states in the automaton
                     [State]
makeInitialStates clo ms s =
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

{-
================================================================================
      End of functions for the local GNBA
================================================================================
-}

-- This parts is used to check if a set is i-elementary
-- and performs other operatios on sets

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
