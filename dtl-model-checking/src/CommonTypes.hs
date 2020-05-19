module  CommonTypes
  (
    --State,
    --Action,
    FiniteGraphRepresentable,
    toGraphviz, -- see if this is the correct way to solve: is not a (visible) method of class ‘FiniteGraphRepresentable’
    subsequencesOfSize,
    ModelCheckingAnswer(..),
    fromModelCheckinganswer,
    extractFromParenthesis,
    getMidleOfExpression,
    getFirstExpression,
    getSecondExpression
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


-- Some utilities

-- receives (Expression) and returns Expression
extractFromParenthesis :: String -> String
extractFromParenthesis string =
  if balancedParenthesis string
     then drop 1 (take (length string - 1) string)
     else error "Parse error. Unbalanced parenthesis"

-- receives (A)operator(B) and returns operator
getMidleOfExpression :: String -> String
getMidleOfExpression ('(':tl) =
  go tl 1 ""
  where go ('(':xs) 0 op   = op
        go ('(':xs) acc op = go xs (acc+1) op
        go (')':xs) acc op = go xs (acc-1) op
        go (x:xs) 0 op     = go xs 0 (op++[x])
        go (x:xs) acc op   = go xs acc op
        go "" _ _          = error "Parse Error. Unbalanced parenthesis"
getMidleOfExpression _ = undefined

-- receives (A)operator(B) returns A
getFirstExpression :: String -> String
getFirstExpression ('(':tl) =
  go tl 1 ""
  where go (')':_) 1 expr = expr
        go ('(':xs) acc expr = go xs (acc+1) (expr++['('])
        go (')':xs) acc expr = go xs (acc-1) (expr++[')'])
        go (x:xs) acc expr   = go xs acc (expr++[x])
        go "" _ _            = error "Parse Error. Unbalanced parenthesis"

-- receives (A)operator(B) returns B
getSecondExpression :: String -> String
getSecondExpression string =
  extractFromParenthesis (drop (2 + (length $ (getFirstExpression string)++(getMidleOfExpression string))) string)

balancedParenthesis :: String -> Bool
balancedParenthesis string =
  go string 0
  where go _ (-1)       = False
        go "" acc       = acc == 0
        go ('(':xs) acc = go xs (acc+1)
        go (')':xs) acc = go xs (acc-1)
        go (_:xs)   acc = go xs acc


subsequencesOfSize :: Int -> [a] -> [[a]]
subsequencesOfSize n xs = let l = length xs
                          in if n>l then [] else subsequencesBySize xs !! (l-n)
 where
   subsequencesBySize [] = [[[]]]
   subsequencesBySize (x:xs) = let next = subsequencesBySize xs
                             in zipWith (++) ([]:next) (map (map (x:)) next ++ [[]])
