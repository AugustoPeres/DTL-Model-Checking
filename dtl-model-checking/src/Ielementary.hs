module Ielementary (SOF, isMaximal, isIConsistent, isLocallyConsistent,
                    isConsistent, downArrow, isIElementary, iElementarySetsAgent,
                    haveSameGlobalFormulas, hasCommunicationFormulas)
where

import qualified Data.Set   as S
import           DTLFormula
import Data.List (nub)
-- DESCRIPTION: This module is responsible for operations over sets of formulas
--              as described in thesis.
--              The operations present here are manly boolean functions that
--              answer questions like:
--                  1. Is the set consistent?
--                  2. Is the set locally consistent?
--              In this module we also create a function that makes all
--              i-elementary sets.
-- NOTE: For efficiency motives, the functions are passed the closure of
--       a formula instead of the formula and then computing the closure
--       internally

-- type Agent is imported from DTL formula

-- SOF stands for Set Of Formulas
type SOF = S.Set Formula


-- -----------------------------------------------------------------------------
-- BEGIN: Construction and manipulation of sets
-- -----------------------------------------------------------------------------

-- | Input: A SOF, an agent, A SOF, a formula
--   Output: all the i-elementary sets for the agent
iElementarySetsAgent :: SOF -> -- ^ the closure of a formula
                        Agent -> -- ^ the agent for which we make the computation
                        SOF -> -- ^ the propositional symbols for the agent
                        GlobalFormula ->
                        [SOF]
iElementarySetsAgent clo i props alpha =
  -- this is probably not the most efficient way to do this
  nub [downArrow set i alpha props | set <- S.toList $ S.powerSet (S.union clo lit),
                                     isIElementary set clo i ]
  where lit = S.union props (S.map negateFormula props)


-- | Input: A set of formulas, an angent, the global formula
--          the set of propositinal symbols for the agent,
--          This last set is very important for the limit case where
--          no propositinal symbols appear in the closure of the formula
--          for the agent
--   Output: A set of formulas with the formulas that are in
--           the domain of the agent
downArrow :: SOF ->
             Agent ->
             GlobalFormula ->
             SOF -> -- the propositional symbols for the agent
             SOF
downArrow set i alpha  props =
  S.filter (\x -> x `S.member` aux0 || isGlobal x) set
  where aux0 = S.union aux lits
        lits = S.union props (S.map negateFormula props)
        aux  = S.union aux2 aux3
        aux2 = S.map negateFormula aux3
        aux3 = S.fromList $ subFormulasAgent alpha i

-- -----------------------------------------------------------------------------
-- END: Construction and manipulation of sets
-- -----------------------------------------------------------------------------




-- -----------------------------------------------------------------------------
-- BEGIN: Queries on the sets
-- -----------------------------------------------------------------------------


-- | Input: A Set
--   Output: True iff that set has a communication formula
hasCommunicationFormulas :: SOF -> Bool
hasCommunicationFormulas set = any (isCommunication) set

-- | Input: Two sets
--   Ouptut: True iff the sets have the same global formulas
haveSameGlobalFormulas :: SOF -> SOF -> Bool
haveSameGlobalFormulas s1 s2 = S.filter isGlobal s1 == S.filter isGlobal s2

-- | Input: A Set, a closure and an agent
--   Output: True iff that set is i-elementary
isIElementary :: SOF -> -- ^ the set we want to check
                 SOF -> -- ^ the closure of a given formula
                 Agent -> -- ^ the agent
                 Bool
isIElementary set clo i=
  isConsistent set clo &&
  isLocallyConsistent set &&
  isIConsistent set clo i &&
  isMaximal set clo


-- | Input: A Set, and the closure
--   Output: True iff the set is consistent
isConsistent :: SOF -> -- ^set we want to check
                SOF -> -- ^closure of the formula
                Bool
isConsistent set clo =
  -- implication
  (all (\f -> if f `S.member` set
        then (getSubFormulasImplication f)!!1 `S.member` set ||
             (negateFormula $ head (getSubFormulasImplication f)) `S.member` set
        else not ((getSubFormulasImplication f)!!1 `S.member` set ||
                  (negateFormula $ head (getSubFormulasImplication f)) `S.member` set))
      (S.filter isImplication clo))
  &&
  -- negation
  (all (\f -> f `S.notMember` set || negateFormula f `S.notMember` set) set)


-- | Input: A Set
--   Output: True iff (Gpsi in s => psi)
isLocallyConsistent :: SOF -> Bool
isLocallyConsistent set =
  all (\f -> not(isGlobally f) || tailFormula f `S.member` set) set


-- Input: A set of formulas and, closure and an agent
-- Output: True iff the set is i- consistent
isIConsistent :: SOF ->
                 SOF ->
                 Agent ->
                 Bool
isIConsistent s clo i =
  all (\x -> (tailFormula x `S.notMember` s || x `S.member` s)
             &&
             (x `S.notMember` s || tailFormula x `S.member` s))
      (S.filter (`isAtAgent` i) clo)


-- Input: A Set of formulas and the closure of a given formula
-- Output: True iff the set is maximal
isMaximal :: SOF -> -- the set we want to check
             SOF -> -- the closure of the formula
             Bool
isMaximal s clo =
  all (\x -> x `S.member` s || negateFormula x `S.member` s) clo
-- -----------------------------------------------------------------------------
-- END: Queries on the sets
-- -----------------------------------------------------------------------------




