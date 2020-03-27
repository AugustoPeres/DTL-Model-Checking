module ROBDD
  (
    ROBDD
  ,
  ) where

import           CommonTypes


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
-- -----------------------------------------------------------------------------
data ROBDD a = Leaf Bool
             | Internal {value :: a, left :: (ROBDD a), right :: (ROBDD a)}
             deriving (Show, Eq)

instance (Show a, Eq a) => FiniteGraphRepresentable (ROBDD a) where
  toGraphviz bdd =
    "Digraph G{\n" ++ helper bdd [] ++ "}"
    where helper :: (Show a, Eq a) => ROBDD a -> [ROBDD a] -> String
          helper (Leaf x) _ = show x
          helper (Internal a (Leaf x) (Leaf z)) _ =
            show a ++ "->" ++ show x ++ "[label = 0]" ++ "\n" ++
            show a ++ "->" ++ show z ++ "[label = 1]" ++ "\n"
          helper b@(Internal a l (Leaf x)) q
            | l `notElem` q =
                show a ++ "->" ++ show x ++ "[label = 1]" ++ "\n" ++
                show a ++ "->" ++ show (value l) ++ "[label = 0]" ++ "\n" ++ helper l (b:l:q)
            | otherwise =
                show a ++ "->" ++ show x ++ "[label = 1]" ++ "\n" ++ "\n" ++
                show a ++ "->" ++ show (value l) ++ "[label = 0]" ++ "\n"
          helper b@(Internal a (Leaf x) r) q
            | r `notElem` q =
                show a ++ "->" ++ show x ++ "[label = 0]" ++ "\n" ++
                show a ++ "->" ++ show (value r) ++ "[label = 1]" ++ "\n" ++ helper r (b:r:q)
            | otherwise =
                show a ++ "->" ++ show x ++ "[label = 0]" ++ "\n" ++ "\n" ++
                show a ++ "->" ++ show (value r) ++ "[label = 1]" ++ "\n"
          helper b@(Internal a l r) q
            | l `notElem` q && r `notElem`q =
                show a ++ "->" ++ show (value l) ++ "[label = 0]" ++ "\n" ++ helper l (b:l:r:q) ++
                show a ++ "->" ++ show (value r) ++ "[label = 1]" ++ "\n" ++ helper r (b:r:l:q)
            | l `notElem` q =
                show a ++ "->" ++ show (value l) ++ "[label = 0]" ++ "\n" ++ helper l (b:l:q) ++
                show a ++ "->" ++ show (value r) ++ "[label = 1]" ++ "\n"
            | r `notElem` q =
                show a ++ "->" ++ show (value l) ++ "[label = 0]" ++ "\n" ++
                show a ++ "->" ++ show (value r) ++ "[label = 1]" ++ "\n" ++ helper r (b:r:q)
            | otherwise =
                show a ++ "->" ++ show (value l) ++ "[label = 0]" ++ "\n" ++
                show a ++ "->" ++ show (value r) ++ "[label = 1]" ++ "\n"

-- -----------------------------------------------------------------------------
-- BEGIN: Algorithms on ROBDD
-- -----------------------------------------------------------------------------
reduce :: ROBDD a -> ROBDD a
reduce = undefined
-- -----------------------------------------------------------------------------
-- END: Algorithms on ROBDD
-- -----------------------------------------------------------------------------
  
-- -----------------------------------------------------------------------------
-- Test instances
-- -----------------------------------------------------------------------------
bdd1 = Internal {value = "x2", left = Leaf True, right = Leaf False}
bdd2 = Internal {value = "x1", left = Leaf True, right = bdd1}
