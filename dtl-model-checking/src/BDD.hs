module BDD
  (
    BDD
  ) where

import           CommonTypes
import qualified Data.IntMap.Strict as M
import Data.Maybe

type NodeID = Int

data BDDNode a = Leaf Bool | Internal a deriving (Show, Eq)


-- We assume that the bdd is always well formed. This is,
-- we assume that the head of the bdd is always at 1.
-- Therefore all functions that change the bdd must always return
-- a well formed bdd
data BDD a = BDD { adjList   :: M.IntMap (Int, Int),
                   valuesMap :: M.IntMap (BDDNode a)
                 } deriving (Show, Eq)


-- -----------------------------------------------------------------------------
-- BEGIN: Getters and checkers for the BDDs
-- -----------------------------------------------------------------------------
getBDDRoot :: BDD a -> BDDNode a
getBDDRoot bdd = fromJust $ M.lookup 1 (valuesMap bdd)

-- -----------------------------------------------------------------------------
-- END: Getters and checkers for the BDDs
-- -----------------------------------------------------------------------------


