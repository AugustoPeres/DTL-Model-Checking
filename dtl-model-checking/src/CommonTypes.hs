module  CommonTypes
  (
    --State,
    --Action,
    FiniteGraphRepresentable,
    toGraphviz, -- see if this is the correct way to solve: is not a (visible) method of class ‘FiniteGraphRepresentable’
    subsequencesOfSize,
    ModelCheckingAnswer(..),
    fromModelCheckinganswer
  ) where

--type State          = Int
--type Action         = String

class FiniteGraphRepresentable a where
  toGraphviz :: a -> String


data ModelCheckingAnswer a = Satisfies | CounterExample a
                           deriving(Show, Eq)

instance Functor ModelCheckingAnswer where
  fmap f (CounterExample a) = CounterExample (f a)
  fmap _ (Satisfies)        = Satisfies


instance Semigroup a => Semigroup (ModelCheckingAnswer a) where
  Satisfies <> b = b
  b <> Satisfies = b
  (CounterExample c1) <> (CounterExample c2) = CounterExample (c1 <> c2)

instance Monoid a => Monoid (ModelCheckingAnswer a) where
  mempty  = Satisfies
  mconcat = foldr (<>) mempty

-- | Input: A model checking answear and a default value
--   Returns: If the answear was satisfies it returns the default value
--            otherwise returns the counter example
fromModelCheckinganswer :: ModelCheckingAnswer a -> a -> a
fromModelCheckinganswer Satisfies def = def
fromModelCheckinganswer (CounterExample a) _ = a


subsequencesOfSize :: Int -> [a] -> [[a]]
subsequencesOfSize n xs = let l = length xs
                          in if n>l then [] else subsequencesBySize xs !! (l-n)
 where
   subsequencesBySize [] = [[[]]]
   subsequencesBySize (x:xs) = let next = subsequencesBySize xs
                             in zipWith (++) ([]:next) (map (map (x:)) next ++ [[]])
