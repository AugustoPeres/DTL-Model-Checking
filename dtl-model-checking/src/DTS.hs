module DTS (DTS, )
where

import qualified Data.Map.Lazy as M
import qualified Data.Set      as S
-- -----------------------------------------------------------------------------
-- BEGIN: Definition of destributed transition system
-- -----------------------------------------------------------------------------

-- This is the representation of transition systems as algebraic data types
-- s -> Denotes the type of the variables that will consist of the sets
-- i -> Denotes the type variable that will be used to represent agent id
-- prop -> Denotes the type variable that will be used to represent the propositional
--         symbols
-- states is just a set of states
-- actions is a mapping from the agents to the actions that are available to them
-- initialStates is a Set of initial sets
-- propSymbols is a mapping from agents to the propositional symbols available to each agent
-- labelingFunction is a mapping from states to a list of sets. Corresponding to each
--                  local labeling function
data DTS s i prop = DTS { states          :: S.Set s,
                          actions         :: M.Map i (S.Set a),
                          initialStates   :: S.Set s,
                          propSymbols     :: M.Map i (S.Set prop),
                          labelingFunctio :: M.Map s ([S.Set])}
-- -----------------------------------------------------------------------------
-- END: Definition of destributed transition system
-- -----------------------------------------------------------------------------

