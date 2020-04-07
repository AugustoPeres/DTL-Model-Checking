module Ielementary (SOF, isMaximal, isIConsistent)
where

import DTLFormula
import qualified Data.Set as S

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
-- BEGIN: Queries on the sets
-- -----------------------------------------------------------------------------

-- Input: A set of formulas and, closure and an agent
-- Output: True iff the set is i- consistent
isIConsistent :: SOF ->
                 SOF ->
                 Agent ->
                 Bool
isIConsistent s clo i =
  all (\x -> (not (tailFormula x `S.member` s) || x `S.member` s)
             &&
             (not (x `S.member` s) || tailFormula x `S.member` s))
      (S.filter (`isAtAgent` i) clo)


-- Input: A Set of formulas and the closure of a given formula
-- Output: True iff the set is maximal
isMaximal :: SOF -> -- the set we want to check
             SOF -> -- the closure of the formula
             Bool
isMaximal s clo =
  all (\x -> not (x `S.member` s) || negateFormula x `S.member` s) clo
-- -----------------------------------------------------------------------------
-- END: Queries on the sets
-- -----------------------------------------------------------------------------




