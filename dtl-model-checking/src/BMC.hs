module BMC ( stateTranslation
           , dtsTranslation
           , trTranslation
           , trStateTranslation
           , actionConditionTranslation)

where

import qualified DTS as T
import SAT.MiniSat
import Data.List ((\\))
import qualified Data.Set as S

-- -----------------------------------------------------------------------------
-- BEGIN: Description
-- -----------------------------------------------------------------------------
-- This module contains the sat reduction used in bounded model checking for DTL

-- -----------------------------------------------------------------------------
-- END: Description
-- -----------------------------------------------------------------------------



-- -----------------------------------------------------------------------------
-- BEGIN: Translation functions
-- -----------------------------------------------------------------------------

-- | Input: A DTS and a bound
--   Output: The encoded transition relation as a boolean formula
dtsTranslation :: ( Ord s, Ord i, Ord prop , Ord a, Show prop, Show a) =>
                  T.DTS s i prop a ->
                  Int ->
                  Formula String
dtsTranslation dts k =
  initCondition :&&:
  (All $ map (trTranslation dts) [0..k]) :&&:
  (All $ map (actionConditionTranslation dts) [0..k])
  where inits = S.toList $ T.initialStates dts
        initCondition = Some (map (stateTranslation dts 0) inits)

-- | Input: A DTS, a value k
--   Output: [[->]]_k^{k + 1} encoded
trTranslation :: (Ord s, Ord i, Ord prop, Ord a, Show prop, Show a) =>
                 T.DTS s i prop a ->
                 Int ->
                 Formula String
trTranslation dts k =
  Some $
  concatMap (trStateTranslation dts k) states
  where states = T.states dts


-- | Input: A DTS,a state, and a value k
--   Output: A list with all the formulas in the transition relation
--           of that state
trStateTranslation :: (Ord s, Ord i, Ord prop, Ord a, Show prop, Show a) =>
                      T.DTS s i prop a ->
                      Int ->
                      s ->
                      [Formula String]
trStateTranslation dts k s =
  foldr (\x y -> y ++
                 [dpstateTran :&&:
                  stateTranslation dts (k + 1) (snd x) :&&:
                  mkaction (fst x)])
        [] neigs
  where neigs = T.getNeighboursWithActions dts s
        dpstateTran = stateTranslation dts k s
        mkaction act = Var $ show act ++ "_" ++ show k


-- |Input: A DTS and a bound k
--  Output: Expresses the condition a_k ==> /\ ~a'_k
--          i.e, only on action per time stamp
actionConditionTranslation :: (Ord s, Ord i, Ord a, Show a) =>
                              T.DTS s i prop a ->
                              Int ->
                              Formula String
actionConditionTranslation dts k =
  All $
  foldr (\x y -> y ++
                 [(Var $ show x ++ "_" ++ show k)
                  :->:
                  (None $ map (\w -> Var $ show w ++ "_" ++ show k) (allActions \\ [x]))])
        [] allActions
  where allActions = T.getAllActions dts


-- | Input: A state a DTS and a bound x
--   Output: The State translation as described in thesis
stateTranslation :: (Ord s, Ord i, Ord prop, Show prop, Ord a) =>
                    T.DTS s i prop a ->
                    Int ->
                    s ->
                    Formula String
stateTranslation dts k s
  | null negVars && null trueVars = No
  | null negVars  = All trueVars
  | null trueVars = None negVars
  | otherwise     = All trueVars :&&: None negVars
  where trueVars = foldr (\x y -> y ++ [Var $ show x ++ "_" ++ show k]) [] symbs
        negVars = foldr (\x y -> y ++ [Var $ show x ++ "_" ++ show k]) [] symbsNotPresent
        symbs = T.getLabel dts s
        symbsNotPresent = T.getAllPropositionalSymbols dts \\ symbs


-- -----------------------------------------------------------------------------
-- END: Translation functions
-- -----------------------------------------------------------------------------






