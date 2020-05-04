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
           , translateFormulaLoop)

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

-- | Input: All the actions for the agent, a GlobaFormula,
--          the point were we want to translate, the bound
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
  | x > k                   = No -- just checking if we are inside the loop
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
  | DTL.isGlobally psi      = translateGloop i acts psi x l k [x]
  | DTL.isEventually psi    = translateFloop i acts psi x l k [x]
  | otherwise               = undefined


translateGloop :: (Show a, Eq a) =>
                  DTL.Agent ->
                  [[a]] ->
                  DTL.Formula ->
                  Int ->
                  Int ->
                  Int ->
                  [Int] -> -- ^ the visited starting points.
                  Formula String
translateGloop i acts psi x l k visited =
  if loopSucc l k x `elem` visited
     then translateLocalFormulaLoop i acts tailF x l k
     else translateLocalFormulaLoop i acts tailF x l k :&&:
          translateGloop i acts psi (loopSucc l k x) l k (x:visited)
  where tailF = DTL.tailFormula psi


translateFloop :: (Show a, Eq a) =>
                  DTL.Agent ->
                  [[a]] ->
                  DTL.Formula ->
                  Int ->
                  Int ->
                  Int ->
                  [Int] -> -- ^ the visited starting points.
                  Formula String
translateFloop i acts psi x l k visited =
  if loopSucc l k x `elem` visited
     then translateLocalFormulaLoop i acts tailF x l k
     else translateLocalFormulaLoop i acts tailF x l k :||:
          translateFloop i acts psi (loopSucc l k x) l k (x:visited)
  where tailF = DTL.tailFormula psi


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

-- | Gives me the successor of a (k, l)-loop
loopSucc :: Int -> -- ^ the value of l
            Int -> -- ^ the bound
            Int -> -- ^ the point where I am
            Int    -- ^ the returned value
loopSucc l k x
  | x == k    = l
  | otherwise = x + 1
