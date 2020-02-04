module  CommonTypes
  (
    State,
    Action,
    FiniteGraphRepresentable,
    toGraphviz, -- see if this is the correct way to solve: is not a (visible) method of class ‘FiniteGraphRepresentable’
    subsequencesOfSize
  ) where

type State          = Int
type Action         = String

class FiniteGraphRepresentable a where
  toGraphviz :: a -> String


subsequencesOfSize :: Int -> [a] -> [[a]]
subsequencesOfSize n xs = let l = length xs
                          in if n>l then [] else subsequencesBySize xs !! (l-n)
 where
   subsequencesBySize [] = [[[]]]
   subsequencesBySize (x:xs) = let next = subsequencesBySize xs
                             in zipWith (++) ([]:next) (map (map (x:)) next ++ [[]])
