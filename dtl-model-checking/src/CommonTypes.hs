module  CommonTypes
  (
    State,
    Action,
    FiniteGraphRepresentable,
    toGraphviz -- see if this is the correct way to solve: is not a (visible) method of class ‘FiniteGraphRepresentable’
  ) where

type State          = Int
type Action         = String

class FiniteGraphRepresentable a where
  toGraphviz :: a -> String
