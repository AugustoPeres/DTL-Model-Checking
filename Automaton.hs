module Automaton
    (
      verifiesImplication
    , verifiesNegation
    ) where

import qualified Data.Set   as Set
import           DTLFormula


-- This parts is used to check if a set is i-elementary or not

{-|
  Implements the down arrow function as describes int the thesis
-}
downArrow :: Set.Set Formula -> Agent -> GlobalFormula -> Set.Set Formula
downArrow b i a = Set.filter (\x -> x `Set.member` formulasAgent || (isGlobal x) ) b
                  where formulasAgent = Set.fromList $ subFormulasAgent a i

{-|
  Checks if a set is i-elementary
-}
isIElementary :: Set.Set Formula ->
                 Agent -> -- agent for wich we check
                 GlobalFormula ->
                 Int -> -- number of agents
                 Bool
isIElementary b i a n = verifiesGlobally b &&
                        verifiesNegation b &&
                        verifiesImplication b a  n &&
                        verifiesIConsistent b i a n &&
                        verifiesMaximal b n a

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
  where helper b (FromGlobal (GNot f)) = not $ Set.member (FromGlobal f) b
        helper b (FromLocal (Not f))   = not $ Set.member (FromLocal f) b
        helper _ _                     = True

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
verifiesMaximal b n a = Set.size b == div (Set.size (closureFormula a n)) 2

psiSetsL1 = PropositionalSymbol "p"
psiSetsL2 = PropositionalSymbol "q"
psiSetsL  = GImplies (Local 1 psiSetsL1) (Local 2 psiSetsL2)
