{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -O2               #-}
module BMC ( stateTranslation
           , dtsTranslation
           , trTranslation
           , trStateTranslation
           , actionConditionTranslation
           , loopTranslation
           , loopConditionTranslation
           , translateFormula
           , translateLocalFormula
           , translateLocalFormulaLoop
           , translateFormulaLoop
           , modelCheck
           , encodeDTSWithFormula
           , modelCheckWithCounterExample
           , witnessTranslation
           , witnessTranslationLoop
           , modelCheckWCE
           , modelCheckUntilK
           )

where

import           Data.List     (intersect, nub, (\\))
import qualified Data.Map.Lazy as M
import           Data.Maybe
import qualified Data.Set      as S
import qualified DTLFormula    as DTL
import qualified DTS           as T
import           SAT.MiniSat

-- -----------------------------------------------------------------------------
-- BEGIN: Description
-- -----------------------------------------------------------------------------
-- This module contains the sat reduction used in bounded model checking for DTL
-- It also contains the model checking algorithm per say
-- -----------------------------------------------------------------------------
-- END: Description
-- -----------------------------------------------------------------------------

type Action = String
-- -----------------------------------------------------------------------------
-- BEGIN: The model checking algorithm and helper functions for it
-- -----------------------------------------------------------------------------

-- | Input: A transition system, a dtl global formula,
--          the number of agents, a staring point and a max bound
--   Output: Tries to find a counter example for k=start, k=start+1 ...
--           until k=maxbound. Returns the counter example as long as the value
--           for which the counter example was found
modelCheckWCE :: (Ord s) =>
                 T.DTS s DTL.Agent DTL.Formula Action ->
                 DTL.GlobalFormula ->
                 Int -> -- ^ the number of agents
                 Int -> -- ^ the starting point
                 Int -> -- ^ the max depth of the search
                 Maybe (M.Map String Bool, Int)
modelCheckWCE dts alpha n start k
  | start > k          = Nothing
  | isNothing solution = modelCheckWCE dts alpha n (start+1) k
  | otherwise          = Just (fromJust solution, start)
  where solution = modelCheckWithCounterExample dts alpha n start


-- | Input: A distributed transition system with
--            * Any type of states
--            * Agents are the agents of the DTL package
--            * Label are formulas (in practice they are literals)
--          A dtl global formula, the number of agents and a bound
--  Output: True iff until the given bound the formula holds
modelCheckWithCounterExample :: (Ord s) =>
                                T.DTS s DTL.Agent DTL.Formula Action ->
                                DTL.GlobalFormula ->
                                Int ->
                                Int ->
                                Maybe (M.Map String Bool)
modelCheckWithCounterExample dts alpha n k =
  solve $ encodeDTSWithFormula newDTS allActions notAlpha k
  where allActions = map (T.getActionsAgent newDTS) [1..n]
        notAlpha   = DTL.makeNNF $ DTL.negateGlobalFormula alpha
        newDTS     = T.fullSimplify dts


-- | Input: A distributed transition system, a formula, the number of agents,
--          and a maximum bound
--   Output: Yes or No depending on the solution. Searches for a solution for
--           k=0, k=1, ..., k=max-bound
modelCheckUntilK :: (Ord s) =>
                    T.DTS s DTL.Agent DTL.Formula Action ->
                    DTL.GlobalFormula ->
                    Int -> -- ^ the number of agents
                    Int -> -- ^ the starting point
                    Int -> -- ^ the max depth of the search
                    Bool
modelCheckUntilK dts alpha n start k
  | start > k = True
  | solution  = modelCheckUntilK dts alpha n (start+1) k
  | otherwise = False
  where solution = modelCheck dts alpha n start


-- | Input: A distributed transition system with
--            * Any type of states
--            * Agents are the agents of the DTL package
--            * Label are formulas (in practice they are literals)
--          A dtl global formula, the number of agents and a bound
--  Output: True iff until the given bound the formula holds
modelCheck :: (Ord s) =>
              T.DTS s DTL.Agent DTL.Formula Action ->
              DTL.GlobalFormula ->
              Int ->
              Int ->
              Bool
modelCheck dts alpha n k =
  not $ satisfiable $ encodeDTSWithFormula newDTS allActions notAlpha k
  where allActions = map (T.getActionsAgent newDTS) [1..n]
        notAlpha   = DTL.makeNNF $ DTL.negateGlobalFormula alpha
        newDTS     = T.fullSimplify dts


-- | Input: A distributed transition system with
--            * Any type of states
--            * Agents are the agents of the DTL package
--            * Label are formulas (in practice they are literals)
--          The actions, a dtl global formula, and a bound
--  Output: The main formula of the model checking
--          algorithm as described in my thesis
encodeDTSWithFormula :: (Ord s) =>
                        T.DTS s DTL.Agent DTL.Formula Action ->
                        [[Action]] -> -- ^ lists with all the action of the agents
                        DTL.GlobalFormula ->
                        Int ->
                        Formula String
encodeDTSWithFormula dts acts alpha k =
  dtsTranslation dts k
  :&&:
  (
    ((Not $ loopConditionTranslation dts k):&&:(witnessTranslation acts alpha k)):||:
    (Some $ map (\l -> loopTranslation dts l k :&&:
                       witnessTranslationLoop acts alpha l k) [0..k])
  )
-- -----------------------------------------------------------------------------
-- END: The model checking algorithm and helper functions for it
-- -----------------------------------------------------------------------------


-- -----------------------------------------------------------------------------
-- BEGIN: Translation functions for transition systems
-- -----------------------------------------------------------------------------

-- | Input: A DTS and a bound
--   Output: The encoded transition relation as a boolean formula
dtsTranslation :: (Ord s, Ord i, Ord prop , Ord a, Show prop, Show a) =>
                  T.DTS s i prop a ->
                  Int ->
                  Formula String
dtsTranslation dts k
  | k == 0   = initCondition
  |otherwise =
    initCondition :&&:
    (All $ map (\x -> trTranslation dts x (x + 1)) [0..(k-1)]) :&&:
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

-- | Input: All the actions for the agents, a GlobalFormula,
--          the bound
--   Output:  The witness translation for non k-loops
witnessTranslation :: (Show a, Eq a) =>
                      [[a]] ->
                      DTL.GlobalFormula ->
                      Int ->
                      Formula String
witnessTranslation acts psi k =
  Some $
  map (\x -> translateFormula acts psi x k) [0..k]


-- | Input: All the actions for the agents, a GlobalFormula,
--          the value of l and the bound
--   Output:  The witness translation for non k-loops
witnessTranslationLoop :: (Show a, Eq a) =>
                          [[a]] ->
                          DTL.GlobalFormula ->
                          Int ->
                          Int ->
                          Formula String
witnessTranslationLoop acts psi l k =
  Some $
  map (\x -> translateFormulaLoop acts psi x l k) [0..k]


-- | Input: All the actions for the agents, a GlobaFormula,
--          the point where we want to translate, the bound
--   Output: The translation as described in my thesis
translateFormula :: (Show a, Eq a) =>
                    [[a]] ->             -- ^ the actions of the agents
                    DTL.GlobalFormula -> -- ^ the global formula we are translating
                    Int ->               -- ^ the point where we are translating
                    Int ->               -- ^ the bound
                    Formula String
translateFormula acts psi x k =
  translateFormulaHelper acts (DTL.wrapGlobal psi) x k

-- | Input: All the actions for all the agents, a Formula,
--          the point were we are translating and the bound
--   Output: The translation to SAT
translateFormulaHelper :: (Show a, Eq a) =>
                          [[a]] ->
                          DTL.Formula ->
                          Int ->
                          Int ->
                          Formula String
translateFormulaHelper acts psi x k
  | DTL.isAtSomeAgent psi = translateLocalFormula agent acts tailF x k
  | DTL.isOr psi          = translateFormulaHelper acts (tails1!!0) x k
                            :||:
                            translateFormulaHelper acts (tails1!!1) x k
  | DTL.isAnd psi         = translateFormulaHelper acts (tails2!!0) x k
                            :&&:
                            translateFormulaHelper acts (tails2!!1) x k
  | otherwise             = undefined
  where tailF  = DTL.tailFormula psi
        tails1 = DTL.getSubFormulasOr psi
        tails2 = DTL.getSubFormulasAnd psi
        agent  = DTL.localAgent psi


-- translations for the local formulas

-- | Input: The agent, all the actions, the formula that
--          we are translating, the point x
--          at where we are translating, and the bound k
--   Translates the formula for that agent
translateLocalFormula :: (Show a, Eq a) =>
                         DTL.Agent ->   -- ^ the agent for which we translate
                         [[a]] ->       -- ^ list with the actions for all agents
                         DTL.Formula -> -- ^ the formula we want to translate
                         Int ->         -- ^ point were we are translating
                         Int ->         -- ^ bound
                         Formula String
translateLocalFormula i acts psi x k
  | x > k                   = No -- just checking if we are inside the bound
  | DTL.isPropSymbol psi    = makeVar psi x
  | DTL.isLiteral psi       = Not $ makeVar (DTL.negateFormula psi) x
  | DTL.isOr psi            = translateLocalFormula i acts ((DTL.getSubFormulasOr psi)!!0) x k
                              :||:
                              translateLocalFormula i acts ((DTL.getSubFormulasOr psi)!!1) x k
  | DTL.isAnd psi           = translateLocalFormula i acts ((DTL.getSubFormulasAnd psi)!!0) x k
                              :&&:
                              translateLocalFormula i acts ((DTL.getSubFormulasAnd psi)!!1) x k
  | DTL.isGlobally psi      = No
  | DTL.isEventually psi    = Some $
                              map (\ w -> translateLocalFormula i acts (DTL.tailFormula psi) w k)
                                  [x..k]
  | DTL.isNext psi          = translateX i acts psi x k
  | DTL.isDualX psi         = translateX i acts psi x k -- translations are equal
  | DTL.isCommunication psi = translateC i acts psi x k
  | DTL.isDualCom psi       = translateDualCom i acts psi x k
  | otherwise               = undefined


translateDualCom :: (Show a, Eq a) =>
                    DTL.Agent ->
                    [[a]] ->
                    DTL.Formula ->
                    Int ->
                    Int ->
                    Formula String
translateDualCom i acts psi x k
  | x == 0    = Yes
  | otherwise =
    (Not $ makeActionOr actionsI 0 (x-1))
    :||:
    (foldr (\w y -> y :&&:
                    (
                      ((Not $ makeActionOr actionsI (w+1) (x-1)) :&&:
                       (makeActionOr actionsI w w))
                      :->:
                      (Not $ makeActionOr actionsJ w w)
                     )
           )
           Yes
          [0..(x-1)])
    :||:
    (foldr (\w y -> y :&&:
                    (
                      (Not $ makeActionOr actionsI (w+1) (x-1) :&&:
                       (makeActionOr actionsI w w))
                      :->:
                      (translateLocalFormula j acts tailF (w+1) k)
                    )
           )
           Yes
           [0..(x-1)])
  where actionsI = acts!!(i-1)
        actionsJ = actionsI `intersect` (acts!!(j-1))
        j        = DTL.dualComAgent psi
        tailF    = DTL.tailFormula psi


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


-- translating in loops

translateFormulaLoop :: (Show a, Eq a) =>
                        [[a]] ->       -- ^ list with all the actions for all agents
                        DTL.GlobalFormula -> -- ^ the formula
                        Int ->         -- ^ The point
                        Int ->         -- ^ value of l
                        Int ->         -- ^ bound
                        Formula String
translateFormulaLoop acts psi x l k =
  translateFormulaLoopHelper acts (DTL.wrapGlobal psi) x l k


-- | Input: All the actions for all the agents, a Formula,
--          the point were we are translating, the value for l
--          and the bound
--   Output: The translation to SAT
translateFormulaLoopHelper :: (Show a, Eq a) =>
                              [[a]] ->       -- ^ list with all the actions for all agents
                              DTL.Formula -> -- ^ the formula
                              Int ->         -- ^ The point
                              Int ->         -- ^ value of l
                              Int ->         -- ^ bound
                              Formula String
translateFormulaLoopHelper acts psi x l k
  | DTL.isAtSomeAgent psi = translateLocalFormulaLoop agent acts tailF x l k
  | DTL.isOr psi          = translateFormulaLoopHelper acts (tails1!!0) x l k
                            :||:
                            translateFormulaLoopHelper acts (tails1!!1) x l k
  | DTL.isAnd psi         = translateFormulaLoopHelper acts (tails2!!0) x l k
                            :&&:
                            translateFormulaLoopHelper acts (tails2!!1) x l k
  | otherwise             = undefined
  where tailF  = DTL.tailFormula psi
        tails1 = DTL.getSubFormulasOr psi
        tails2 = DTL.getSubFormulasAnd psi
        agent  = DTL.localAgent psi


-- | Input: An agent, all the actions of all agents, a DTL formula
--          the point, the value of l, the bound
--   Output: The translation of the formula.
translateLocalFormulaLoop :: (Show a, Eq a) =>
                            DTL.Agent ->   -- ^ the agent
                            [[a]] ->       -- ^ all the actions
                            DTL.Formula -> -- ^ the formula
                            Int ->         -- ^ the point
                            Int ->         -- ^ the value of l
                            Int ->         -- ^ the bound
                            Formula String
translateLocalFormulaLoop i acts psi x l k
  | DTL.isPropSymbol psi    = makeVar psi x
  | DTL.isLiteral psi       = Not $ makeVar (DTL.negateFormula psi) x
  | DTL.isOr psi            =
    translateLocalFormulaLoop i acts ((DTL.getSubFormulasOr psi)!!0) x l k
    :||:
    translateLocalFormulaLoop i acts ((DTL.getSubFormulasOr psi)!!1) x l k
  | DTL.isAnd psi           =
    translateLocalFormulaLoop i acts ((DTL.getSubFormulasAnd psi)!!0) x l k
    :&&:
    translateLocalFormulaLoop i acts ((DTL.getSubFormulasAnd psi)!!1) x l k
  | DTL.isGlobally psi      = translateGloop i acts psi x l k
  | DTL.isEventually psi    = translateFloop i acts psi x l k
  | DTL.isNext psi          = translateXloop i acts psi x l k
  | DTL.isDualX psi         = translateNloop i acts psi x l k
  | DTL.isCommunication psi = translateCloop i acts psi x l k
  | DTL.isDualCom psi       = translateDualComloop i acts psi x l k
  | otherwise               = undefined


translateDualComloop :: (Show a, Eq a) =>
                        DTL.Agent ->
                        [[a]] ->
                        DTL.Formula ->
                        Int ->
                        Int ->
                        Int ->
                        Formula String
translateDualComloop i acts psi x l k
  | x == 0    = Yes
  | otherwise =
    -- the case where no actions are actions of agent i
    (Not $ makeActionOrList actionsI (nub $ map rho0 [0..(x-1)]))
    -- the last action is not an action of the agent j
    :||:
    (
      foldr (\w y -> y :&&:
                     (
                       ((Not $ makeActionOrList actionsI (nub $ map (\t->rho0 $ x-t-1) [0..(w-1)])):&&:
                        (makeActionOr actionsI (rho0 $ x-w-1) (rho0 $ x-w-1)))
                       :->:
                       (Not $ makeActionOr actionsI (rho0 $ x-w-1) (rho0 $ x-w-1))
                     )
            )
            Yes
            times
    )
    -- the case where the formula holds
    :||:
    (
      foldr (\w y -> y :&&:
                     (
                       ((Not $ makeActionOrList actionsI (nub $ map (\t->rho0 $ x-t-1) [0..(w-1)])):&&:
                        (makeActionOr actionsI (rho0 $ x-w-1) (rho0 $ x-w-1)))
                       :->:
                       (translateLocalFormulaLoop j acts tailF (rho' $ x-w) l k)
                     )
            )
            Yes
            times
    )
  where actionsI = acts!!(i-1)
        actionsJ = acts!!(j-1)
        j        = DTL.communicationAgent psi
        tailF    = DTL.tailFormula psi
        rho0     = rho k l 0
        rho'     = rho k l (DTL.majorationPTH tailF)
        times    = makeIndexesForBackCom l k x


translateCloop :: (Show a , Eq a) =>
                  DTL.Agent ->
                  [[a]] ->
                  DTL.Formula ->
                  Int ->
                  Int ->
                  Int ->
                  Formula String
translateCloop i acts psi x l k
  | x == 0    = No
  | otherwise =
    foldr (\w y -> y :&&:
                   (
                     ((Not $ makeActionOrList actionsI (nub $ map (\t->rho0 $ x-t-1) [0..(w-1)])):&&:
                      makeActionOr actionsI (rho0 $ x - w - 1) (rho0 $ x - w - 1)
                     )
                     :->:
                     ((translateLocalFormulaLoop j acts tailF (rho' $ x - w) l k):&&:
                      (makeActionOr actionsJ (rho0 $ x - w - 1) (rho0 $ x - w - 1))
                     )
                   )

          )
          (makeActionOrList actionsI (map rho0 times))
          (times)
  where actionsI = acts!!(i-1)
        actionsJ = actionsI `intersect` (acts!!(j-1))
        j        = DTL.communicationAgent psi
        tailF    = DTL.tailFormula psi
        rho0     = rho k l 0
        rho'     = rho k l (DTL.majorationPTH tailF)
        times    = makeIndexesForBackCom l k x


translateNloop :: (Show a, Eq a) =>
                  DTL.Agent ->
                  [[a]] ->
                  DTL.Formula ->
                  Int ->
                  Int ->
                  Int ->
                  Formula String
translateNloop i acts psi x l k
  | x <= l =
    translateXloop i acts psi x l k
    :||:
    (Not $ makeActionOr actionsAgent x k)
  | otherwise =
    translateXloop i acts psi x l k
    :||:
    (Not $ makeActionOrList actionsAgent (map (rho0) [x..(x+p-1)]))
  where actionsAgent = acts!!(i-1)
        p            = k - l + 1
        rho0         = rho k l 0


translateXloop :: (Show a, Eq a) =>
                  DTL.Agent ->
                  [[a]] ->
                  DTL.Formula ->
                  Int ->
                  Int ->
                  Int ->
                  Formula String
translateXloop i acts psi x l k
  | x <= l =
    foldr (\w y -> y :&&: (
                           (
                             (Not $ makeActionOr actionsAgent x (w-1))
                             :&&:
                             makeActionOr actionsAgent w w
                            )
                           :->:
                           translateLocalFormulaLoop i acts (tailF) (rho' (w + 1)) l k)
           )
          (makeActionOr actionsAgent x k)
          [x..k]
  | otherwise =
    foldr (\w y -> y :&&: (
                           (
                             (Not $ makeActionOrList actionsAgent (map (rho0) [x..(w-1)]) )
                             :&&:
                             makeActionOr actionsAgent (rho0 w) (rho0 w)
                            )
                           :->:
                           translateLocalFormulaLoop i acts (tailF) (rho' (w+1)) l k)
           )
          (makeActionOr actionsAgent l k)
          [x..(x+p-1)]
  where tailF        = DTL.tailFormula psi
        actionsAgent = acts!!(i-1)
        p            = k - l + 1
        rho0         = rho k l 0
        rho'         = rho k l (DTL.majorationPTH (DTL.tailFormula psi))


translateGloop :: (Show a, Eq a) =>
                  DTL.Agent ->
                  [[a]] ->
                  DTL.Formula ->
                  Int ->
                  Int ->
                  Int ->
                  Formula String
translateGloop i acts psi x l k =
  All $
  map
  (\t -> translateLocalFormulaLoop i acts subf (rho' t) l k)
  (makeRelevantInterval x rho')
  where rho' = rho k l pth
        rb   = k + pth*p
        p    = k - l + 1
        pth  = DTL.majorationPTH (DTL.tailFormula psi)
        subf = DTL.tailFormula psi


translateFloop :: (Show a, Eq a) =>
                  DTL.Agent ->
                  [[a]] ->
                  DTL.Formula ->
                  Int ->
                  Int ->
                  Int ->
                  Formula String
translateFloop i acts psi x l k =
  Some $
  map
  (\t -> translateLocalFormulaLoop i acts subf (rho' t) l k)
  (makeRelevantInterval x rho')
  where rho' = rho k l pth
        rb   = k + pth*p
        p    = k - l + 1
        pth  = DTL.majorationPTH (DTL.tailFormula psi)
        subf = DTL.tailFormula psi

-- -----------------------------------------------------------------------------
-- END: Translation of formulas
-- -----------------------------------------------------------------------------



-- some helper function

-- The projection as defined in my thesis
rho :: Int -> -- the value of k
       Int -> -- the value of l
       Int -> -- the number of the border
       Int -> -- the point in time
       Int    -- the returned projection
rho k l n x
  | x <= border = x
  | otherwise   = rho k l n (x - p)
  where border = k + n*p
        p = k - l + 1

-- Receives a value for x and a rho.
-- Returns the list [x..t] where t is the first point
-- whose sucssessor appears repeated
makeRelevantInterval :: Int ->          -- the time point
                        (Int -> Int) -> -- the value of rho
                        [Int]           -- the returned interval
makeRelevantInterval x r =
  go [r x]
  where go l =
          if r (last l + 1) `elem` l
             then l
             else go $ l ++ [r (last l + 1)]

-- Returns the indexes for the relevant action in the comunication
-- formulas
makeIndexesForBackCom :: Int -> -- value of k
                         Int -> -- value of l
                         Int -> -- value of x
                         [Int]
makeIndexesForBackCom l k x
  | x <= k    = [0..(x-1)]
  | otherwise = [0..(p-1)] ++ [(x-l)..(x-1)]
  where p = k - l + 1

-- returns the interval [t..x]
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

-- makes a formula of the type OR(0_v1 ...) for a given
-- list of variables and a list of indexes. The same as the
-- the previous function but using a list instead of bounds
-- TODO: SShould nub the list in order to not repeat variables
makeActionOrList :: Show act => [act] -> [Int] -> Formula String
makeActionOrList acts list =
  Some $ foldr (\action y -> y ++ map (makeVar action) list)
               []
               acts
