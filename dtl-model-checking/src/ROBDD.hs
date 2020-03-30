module ROBDD
  (
    ROBDD
  ,
  ) where

import           CommonTypes
import Data.Functor
import Data.List (union)

data OperationBDD = AND | OR deriving (Show, Eq)

-- NOTE: Use memoisation by performing calls only on one the left side of any binary decison
--       diagram first and only then moving to the right side.
--       This should be better than going over all branches at the same time.
--       Maybe I should create a stack with values and then removing calls that
--       appear twice


-- -----------------------------------------------------------------------------
-- Recursive implementation of binary decision diagrams
-- A bdd is either a leaf or an internal node pointing to other two binary
-- decision diagrms.
-- value: is the variabe labeling the node
-- left: left child
-- right: right child
-- NOTE: there is no constraint in the class that ensures that whatever the user
--       defines is a reduced ordered binary decision diagram.
--       For that we must define a function reduce
--       reduce :: ROBDD -> ROBDD
--       that receives what should be a ROBDD and returns something that we are
--       sure to be a binary decision diagram.
-- NOTE: the code generating nodes must ensure unique labels, otherwise the
--       the algorithms will not work.
-- -----------------------------------------------------------------------------
data ROBDD a lb = Leaf Bool
                | Internal {value :: a, label :: lb, left :: (ROBDD a lb), right :: (ROBDD a lb)}
                deriving (Show)

instance Eq lb => Eq (ROBDD a lb) where
  (Leaf b) == (Leaf b') = b == b'
  (Internal _ lb _ _) == (Internal _ lb' _ _) = lb == lb'
  (Internal _ _ _ _) == (Leaf _) = False
  (Leaf _) == (Internal _ _ _ _) = False


instance (Eq a, Ord a, Eq lb) => Ord (ROBDD a lb) where
  (Internal a _ _ _) `compare` (Internal a' _ _ _) = a `compare` a'
  compare (Internal _ _ _ _) (Leaf _) = LT
  compare (Leaf _) (Internal _ _ _ _) = GT
  compare (Leaf _) (Leaf _)         = EQ
  (Internal a _ _ _) < (Internal a' _ _ _) = a < a'
  (Internal _ _ _ _) < (Leaf _) = True -- leafs are always at the highest level.
  (Leaf _) < (Internal _ _ _ _) = False
  (Leaf _) < (Leaf _) = False -- leafs have the same order

instance (Show a, Show lb, Eq lb) => FiniteGraphRepresentable (ROBDD a lb) where
  toGraphviz bdd =
    "Digraph {\n" ++
    foldr f "" nodes ++
    foldr g "" nodes ++
    "}"
    where nodes = dfs bdd
          g (Leaf _) str = str
          g (Internal v l _ _) str = str ++ show l ++ " [label = " ++ show v ++"]\n" 
          f (Leaf _) str = str
          f (Internal _ lbl (Leaf b) (Leaf b')) str =
            str ++
            show lbl ++ "->" ++ show b ++ "[label = 0]\n" ++
            show lbl ++ "->" ++ show b' ++ "[label = 1]\n"
          f (Internal _ lbl (Leaf b) r) str =
            str ++
            show lbl ++ "->" ++ show b ++ "[label = 0]\n" ++
            show lbl ++ "->" ++ show (label r) ++ "[label = 1]\n"
          f (Internal _ lbl l (Leaf b)) str =
            str ++
            show lbl ++ "->" ++ show b ++ "[label = 1]\n" ++
            show lbl ++ "->" ++ show (label l) ++ "[label = 0]\n"
          f (Internal _ lbl l r) str =
            str ++
            show lbl ++ "->" ++ show (label l) ++ "[label = 0]\n" ++
            show lbl ++ "->" ++ show (label r) ++ "[label = 1]\n"


            
   
-- -----------------------------------------------------------------------------
-- BEGIN: Algorithms on ROBDD
-- -----------------------------------------------------------------------------

-- | Input: A BDD
--   Output: A list with all the sub bdds in descending order
--   Method: BFS. We check for equality. Therefore a BDD
--           is added to the Q iff it is not there yet. Therefore we never
--           visit nodes more than once
dfs :: (Eq lb) => ROBDD a lb -> [ROBDD a lb]
dfs bdd = helper [bdd] (getChildren bdd)
  where helper visited [] = visited
        helper visited (q:qs) = helper (visited ++ [q]) (qs `union` getChildren q)


getChildren :: ROBDD a lb -> [ROBDD a lb]
getChildren (Leaf _) = []
getChildren (Internal _ _ l r) = [l, r]


-- | Input: a Binary decision diagram
--   Returns: The same BDD but with labels in order.

-- -----------------------------------------------------------------------------
-- END: Algorithms on ROBDD
-- -----------------------------------------------------------------------------


-- -----------------------------------------------------------------------------
-- Test instances
-- -----------------------------------------------------------------------------
bdd1 = Internal {value = "x2", label = 1, left = Leaf True, right = Leaf False}
bdd2 = Internal {value = "x1", label = 2, left = Leaf True, right = bdd1}


-- This nodes are to test the reduce algorithm
n6 = Internal "x3" 1 (Leaf False) (Leaf False)
n5 = Internal "x3" 2 (Leaf True) (Leaf False)
n4 = Internal "x3" 3 (Leaf True) (Leaf True)
n3 = Internal "x2" 4 n6 n6
n2 = Internal "x2" 5 n5 n4
n1 = Internal "x1" 6 n3 n2

-- to show that one reduce might not be enough
bddRed = Internal "x1" 1 (Internal "x2" 2 (Leaf True) (Leaf True)) (Leaf True)
-- End of reduce tests

-- examples from the book
exempOne4 = Internal "x4" 1 (Leaf False) (Leaf True)
exempOne3 = Internal "x3" 2 exempOne4 (Leaf (True))
exempOne2 = Internal "x2" 3 exempOne4 exempOne3
exempOne = Internal  "x1" 4 exempOne2 exempOne3

exempTwo3 = Internal "x4" 1 (Leaf False) (Leaf True)
exempTwo2 = Internal "x3" 2 exempTwo3 (Leaf True)
exempTwo = Internal  "x1" 3 exempOne4 exempOne3
-- end examples from the book
