module BMC ( stateTranslation
           , dtsTranslation
           , trTranslation
           , trStateTranslation
           , actionConditionTranslation
           , loopTranslation
           , loopConditionTranslation
           , translateFormula
           , translateLocalFormula)

where

import           Data.List   ((\\), intersect)
import qualified Data.Set    as S
import qualified DTLFormula  as DTL
import qualified DTS         as T
import           SAT.MiniSat

-- -----------------------------------------------------------------------------
-- BEGIN: Description
-- -----------------------------------------------------------------------------
-- This module contains the sat reduction used in bounded model checking for DTL

-- -----------------------------------------------------------------------------
-- END: Description
-- -----------------------------------------------------------------------------



-- -----------------------------------------------------------------------------
-- BEGIN: Translation functions for transition systems
-- -----------------------------------------------------------------------------

-- | Input: A DTS and a bound
--   Output: The encoded transition relation as a boolean formula
dtsTranslation :: ( Ord s, Ord i, Ord prop , Ord a, Show prop, Show a) =>
                  T.DTS s i prop a ->
                  Int ->
                  Formula String
dtsTranslation dts k =
  initCondition :&&:
  (All $ map (\x -> trTranslation dts x (x + 1)) [0..k]) :&&:
  (All $ map (actionConditionTranslation dts) [0..k])
  where inits = S.toList $ T.initialStates dts
        initCondition = Some (map (stateTranslation dts 0) inits)

-- | Input: A DTS, a value l and a value k
--   Output: [[->]]_l^{k} encoded
trTranslation :: (Ord s, Ord i, Ord prop, Ord a, Show prop, Show a) =>
                 T.DTS s i prop a ->
                 Int ->
                 Int ->
                 Formula String
trTranslation dts l k =
  Some $
  concatMap (trStateTranslation dts l k) states
  where states = T.states dts


-- | Input: A DTS,a state, a value l, and a value k
--   Output: A list with all the formulas in the transition relation
--           of that state. This is responsible for the codification
--           of the translation s at step l to s at step k
trStateTranslation :: (Ord s, Ord i, Ord prop, Ord a, Show prop, Show a) =>
                      T.DTS s i prop a ->
                      Int ->
                      Int ->
                      s ->
                      [Formula String]
trStateTranslation dts l k s =
  foldr (\x y -> y ++
                 [dpstateTran :&&:
                  stateTranslation dts (k) (snd x) :&&:
                  mkaction (fst x)])
        [] neigs
  where neigs = T.getNeighboursWithActions dts s
        dpstateTran = stateTranslation dts l s
        mkaction act = makeVar act l


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
                 [(makeVar x k)
                  :->:
                  (None $
                   map (\w -> makeVar w k)
                       (allActions \\ [x]))])
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
  where trueVars = foldr (\x y -> y ++ [makeVar x k]) [] symbs
        negVars = foldr (\x y -> y ++ [makeVar x k]) [] symbsNotPresent
        symbs = T.getLabel dts s
        symbsNotPresent = T.getAllPropositionalSymbols dts \\ symbs


-- | Input: A DTS, two ints
--   Output: l_L^k as described in the thesis
loopTranslation :: (Ord s, Ord i, Ord prop, Show prop, Ord a, Show a) =>
                  T.DTS s i prop a ->
                  Int -> -- ^ the value for l
                  Int -> -- ^ the value for k
                  Formula String -- ^ the translated formula
loopTranslation dts l k = trTranslation dts k l


-- | Input: A DTS , a value for a bound
--   Output: The loop condition as described in the thesis
loopConditionTranslation :: (Ord s, Ord i, Ord prop, Show prop, Ord a, Show a) =>
                            T.DTS s i prop a ->
                            Int ->
                            Formula String
loopConditionTranslation dts k =
  Some $ foldr (\l y -> y ++ [loopTranslation dts l k]) [] [0..k]


-- -----------------------------------------------------------------------------
-- END: Translation functions for transition systems
-- -----------------------------------------------------------------------------

-- -----------------------------------------------------------------------------
-- BEGIN: Translation of formulas
-- -----------------------------------------------------------------------------

-- | Input: A global formula, the actions of the agents
--   Output: The translation to SAT
translateFormula :: Show a =>
                    DTL.Formula ->
                    [[a]] ->
                    Formula String
translateFormula _ _ = undefined


-- translations for the local formulas

-- | Input: A formula, all the actions, the agent
--          for which we are translating, the point x
--          at where we are translating, and the bound k
--   Translates the formula for that agent
translateLocalFormula :: (Show a, Eq a) =>
                         DTL.Agent ->
                         [[a]] ->
                         DTL.Formula ->
                         Int ->
                         Int ->
                         Formula String
translateLocalFormula i acts psi x k
  | DTL.isPropSymbol psi    = makeVar psi x
  | DTL.isLiteral psi       = Not $ makeVar (DTL.negateFormula psi) x
  | DTL.isGlobally psi      = No
  | DTL.isNext psi          = translateX i acts psi x k
  | DTL.isCommunication psi = translateC i acts psi x k



translateC :: (Show a, Eq a) =>
              DTL.Agent ->
              [[a]] ->
              DTL.Formula ->
              Int ->
              Int ->
              Formula String
translateC i acts psi x k
  | x == 0    = No
  | otherwise =
    foldr (\w y -> y :&&: (
                          (
                            (Not (makeActionOr actionsI (w+1) (x-1))) :&&:
                            makeActionOr actionsI w w
                          )
                          :->:
                          ( translateLocalFormula j acts tailF (w+1) k :&&:
                            makeActionOr actionsJ w w
                          )
                          )
          )
          (makeActionOr actionsI 0 (x - 1))
          [0..(x - 1)]
  where actionsI = acts!!(i-1)
        actionsJ = actionsI `intersect` (acts!!(j-1))
        j        = DTL.communicationAgent psi
        tailF    = DTL.tailFormula psi


translateX :: (Show a, Eq a) =>
              DTL.Agent ->
              [[a]] ->
              DTL.Formula ->
              Int ->
              Int ->
              Formula String
translateX i acts psi x k =
  -- Now the series of implications --
  foldr (\w y -> y :&&: (
                         (
                           (Not $ makeActionOr actionsAgent x (w-1))
                           :&&:
                           makeActionOr actionsAgent w w
                          )
                         :->:
                         translateLocalFormula i acts (tailF) (w + 1) k)
         )
        (makeActionOr actionsAgent x (k - 1))
        [x..(k-1)]
  where actionsAgent = acts!!(i-1)
        tailF = DTL.tailFormula psi
-- -----------------------------------------------------------------------------
-- END: Translation of formulas
-- -----------------------------------------------------------------------------



-- some helper function

-- receives some symbol and point
-- returns a var of the format (Var point_symbol)
makeVar :: Show v => v -> Int -> Formula String
makeVar v x = Var $ show x ++ "_" ++ show v

-- makes a formula of the type OR( 0_v1 0_v2 1_v1 1_v2)
-- for the given list of variables and bounds
makeActionOr :: Show act => [act] -> Int -> Int -> Formula String
makeActionOr acts x k =
  Some $ foldr (\action y -> y ++ map (makeVar action) [x..k])
               []
               acts

