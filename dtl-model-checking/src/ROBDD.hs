module ROBDD
  (
    ROBDD
  ,
  ) where

import           CommonTypes
import           Data.List     (union, (\\))
import           Data.List     (delete, dropWhile, nub, sort, sortBy)
import qualified Data.Map.Lazy as M
import           Data.Maybe

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
data ROBDD a lb = Leaf Bool lb -- we label the leaf to make it easier on the pairing function
                | Internal {value :: a, label :: lb, left :: (ROBDD a lb), right :: (ROBDD a lb)}
                deriving (Show)


-- TODO: Change this class to common types if there are any more types
-- that would benefit from this class
class Bifunctor f where
  bimap :: (Eq c, Ord c) =>
           (a -> b) ->
           (c -> d) ->
           f a c ->
           f b d
  firstmap :: (Eq c, Ord c) =>
              (a -> b) ->
              f a c ->
              f b c
  secondmap :: (Eq c, Ord c) =>
              (c -> d) ->
              f a c ->
              f a d

-- Now I want ot instance functor to be able to map over the bdd
-- more easily. And making sure that i am using memoisation
-- to keep track of all the changes.
--
-- Here we instance functor that works just over the values.
-- We do not want any operations to be done over the leafs
instance Bifunctor (ROBDD) where
  firstmap f bdd = bimap f id bdd
  secondmap f bdd = bimap id f bdd
  bimap f h bdd =
    fMemo f h bdd
    where -- defining here the function that uses open recursion
          open :: ((a -> a') -> (lb -> lb') -> ROBDD a lb -> ROBDD a' lb') -> -- this is the function that
                                                                              -- we want to open
                  (a -> a') -> -- This is the first function that we pass to opened
                  (lb -> lb') -> -- This is the second function that we pass to opened
                  ROBDD a lb -> -- the binary decision diagram we want to change
                  ROBDD a' lb'
          open _ _ g2 (Leaf b v) = Leaf b (g2 v)
          open opened g1 g2 (Internal v lbl l r) = Internal (g1 v) (g2 lbl) (opened g1 g2 l) (opened g1 g2 r)
          -- now we define the map to keep track of the recursive calls --
          -- In the map we store the call to open fMemo g1 g1 bdd in function of the label
          -- of the bdd we are using
          -- On the other hand open calls fMemo when not at the leaf levels
          -- this causes fMemo to consult the dictionary again for a smaller bdd
          -- until we reach the leafs.
          -- Because the entries in any dictionary are unique we make sure that
          -- every call to open fMemo _ _ _ is only evaluated once.
          -- For example if A has left node B and C has left node B then
          -- opened f g1 g2 A is A _ _ (fMemo B) _ and
          -- opened f g1 g2 C is C _ _ (fMemo B) _
          -- Therefore we are allocating less memory and making less evaluations of the function
          mapMemo = M.fromList [(getLabel b, open fMemo f h b) | b <- dfs bdd]
          fMemo _ _ x = fromJust $ M.lookup (getLabel x) mapMemo


instance Eq lb => Eq (ROBDD a lb) where
  (Leaf _ b) == (Leaf _ b') = b == b'
  (Internal _ lb _ _) == (Internal _ lb' _ _) = lb == lb'
  (Internal _ _ _ _) == (Leaf _ _) = False
  (Leaf _ _) == (Internal _ _ _ _) = False


instance (Eq a, Ord a, Eq lb) => Ord (ROBDD a lb) where
  (Internal a _ _ _) `compare` (Internal a' _ _ _) = a `compare` a'
  compare (Internal _ _ _ _) (Leaf _ _) = LT
  compare (Leaf _ _) (Internal _ _ _ _) = GT
  compare (Leaf _ _) (Leaf _ _)         = EQ
  (Internal a _ _ _) < (Internal a' _ _ _) = a < a'
  (Internal _ _ _ _) < (Leaf _ _) = True -- leafs are always at the highest level.
  (Leaf _ _) < (Internal _ _ _ _) = False
  (Leaf _ _) < (Leaf _ _) = False -- leafs have the same order

instance (Show a, Show lb, Eq lb) => FiniteGraphRepresentable (ROBDD a lb) where
  toGraphviz bdd =
    "Digraph {\n" ++
    foldr f "" nodes ++
    foldr g "" nodes ++
    "}"
    where nodes = dfs bdd
          g (Leaf b l) str = str ++ show l ++ " [label = " ++ show b ++ "]\n"
          g (Internal v l _ _) str = str ++ show l ++ " [label = " ++ show v ++"]\n"
          f (Leaf _ _) str = str
          f (Internal _ lbl (Leaf _ l) (Leaf _ l')) str =
            str ++
            show lbl ++ "->" ++ show l ++ "[label = 0]\n" ++
            show lbl ++ "->" ++ show l' ++ "[label = 1]\n"
          f (Internal _ lbl (Leaf _ l) r) str =
            str ++
            show lbl ++ "->" ++ show l ++ "[label = 0]\n" ++
            show lbl ++ "->" ++ show (label r) ++ "[label = 1]\n"
          f (Internal _ lbl l (Leaf _ l')) str =
            str ++
            show lbl ++ "->" ++ show l' ++ "[label = 1]\n" ++
            show lbl ++ "->" ++ show (label l) ++ "[label = 0]\n"
          f (Internal _ lbl l r) str =
            str ++
            show lbl ++ "->" ++ show (label l) ++ "[label = 0]\n" ++
            show lbl ++ "->" ++ show (label r) ++ "[label = 1]\n"




-- -----------------------------------------------------------------------------
-- BEGIN: Algorithms on ROBDD
-- -----------------------------------------------------------------------------

-- | Returns True iff the bdd is a lead
isLeaf :: ROBDD a lb -> Bool
isLeaf (Leaf _ _) = True
isLeaf _          = False


-- | Input: A BDD
--   Output: A list with all the sub bdds in descending order
--   Method: BFS. We check for equality. Therefore a BDD
--           is added to the Q iff it is not there yet. Therefore we never
--           visit nodes more than once
dfs :: (Eq lb) => ROBDD a lb -> [ROBDD a lb]
dfs bdd = helper [bdd] (getChildren bdd)
  where helper visited [] = visited
        helper visited (q:qs) = helper (visited ++ [q]) (qs `union` (getChildren q \\ visited))


-- Input: Two Binary decision Diagrams
-- Output: The binary decision diagram resulting from the application of apply
-- NOTE: Note to be exported. This is just used to memoise in the larger function
applyNoMemoise :: (Ord a, Eq lb) =>
                  OperationBDD -> -- ^Operation to be applied
                  ROBDD a lb -> -- ^First BDD
                  ROBDD a lb -> -- ^Second Memoise
                  ROBDD a (lb, lb) -- ^Third BDD. Using (lb, lb) to make combining labels easy
applyNoMemoise o (Leaf b lb) (Leaf b' lb') = if o == AND then Leaf (b && b') (lb, lb') else Leaf (b || b') (lb, lb')
applyNoMemoise o (Internal v lb l r) leaf@(Leaf b lb')
  | o == OR = if b == True
              then Leaf True (lb, lb')
              else Internal v (lb, lb') (applyNoMemoise o l leaf) (applyNoMemoise o r leaf)
  | o == AND = if b == True
               then Internal v (lb, lb') (applyNoMemoise o l leaf) (applyNoMemoise o r leaf)
               else Leaf False (lb, lb')
applyNoMemoise o leaf@(Leaf b lb) (Internal v lb' l r)
  | o == OR = if b == True
              then Leaf True (lb, lb')
              else Internal v (lb, lb') (applyNoMemoise o leaf l) (applyNoMemoise o leaf r)
  | o == AND = if b == True
               then Internal v (lb, lb') (applyNoMemoise o leaf l) (applyNoMemoise o leaf r)
               else Leaf False (lb, lb')
applyNoMemoise o n1@(Internal v lb l r) n2@(Internal v' lb' l' r')
  | n1 < n2 = Internal v (lb, lb') (applyNoMemoise o l n2) (applyNoMemoise o r n2)
  | n2 < n1 = Internal v' (lb, lb') (applyNoMemoise o l' n1) (applyNoMemoise o r' n1)
  | otherwise = Internal v (lb, lb') (applyNoMemoise o l l') (applyNoMemoise o r r')


-- | Applies the operation to both bdds
--   This function uses the fact that haskell uses lazy evaluation
--   in order to memomize.
--   NOTE: If this is not memoizing check the book high performance haskell for a solution
apply :: (Ord a, Eq lb, Ord lb) =>
         OperationBDD ->
         ROBDD a lb ->
         ROBDD a lb ->
         ROBDD a (lb , lb) -- note, maybe it would be more useful to allow for diferent types of labels
apply op bdd1 bdd2 =
  faster op bdd1 bdd2
  where -- open recursion --
        h _ o (Leaf b lb) (Leaf b' lb') = if o == AND then Leaf (b && b') (lb, lb') else Leaf (b || b') (lb, lb')
        h f o (Internal v lb l r) leaf@(Leaf b lb')
          | o == OR = if b == True
                         then Leaf True (lb, lb')
                         else Internal v (lb, lb') (f o l leaf) (f o r leaf)
          | o == AND = if b == True
                          then Internal v (lb, lb') (f o l leaf) (f o r leaf)
                          else Leaf False (lb, lb')
        h f o leaf@(Leaf b lb) (Internal v lb' l r)
          | o == OR = if b == True
                         then Leaf True (lb, lb')
                         else Internal v (lb, lb') (f o leaf l) (f o leaf r)
          | o == AND = if b == True
                          then Internal v (lb, lb') (f o l leaf) ( f  o r leaf)
                          else Leaf False (lb, lb')
        h f o n1@(Internal v lb l r) n2@(Internal v' lb' l' r')
          | n1 < n2 = Internal v (lb, lb') (f  o l n2) (f  o r n2)
          | n2 < n1 = Internal v' (lb, lb') (f  o n1 l') (f  o n1 r')
          | otherwise = Internal v (lb, lb') (f  o l l') (f  o r r')
        -- map --
        -- The entries in the map correspond to all the possible different
        -- call the the function.
        mapMemo = M.fromList [((getLabel r, getLabel s), h faster op r s) | r <- dfs bdd1, s <- dfs bdd2]
        faster _ x y = fromJust $ (M.lookup (getLabel x, getLabel y) mapMemo)

-- | Input: a Binary decision diagram
--   Returns: The same BDD but with labels as Ints and ordered.
normalizeLabels :: (Eq lb, Ord lb, Ord a) => ROBDD a lb -> ROBDD a Int
normalizeLabels bdd =
  secondmap (\x -> fromJust $ M.lookup x m) bdd
  where m = M.fromList $ zip (map getLabel (sort $ dfs bdd)) [1..]


-- | Input: Two binary decision diagrams
--   Output True iff they are isomorphic
--   NOTE: Once again we use memoization and open
--         recursion to avoid making evaluating the same bdd
isomorphicQ :: (Eq a, Ord lb) =>
               ROBDD a lb ->
               ROBDD a lb ->
               Bool
isomorphicQ bdd1 bdd2 =
  memoized bdd1 bdd2
  where memoized x y = fromJust $ M.lookup (getLabel x, getLabel y) memoMap
        memoMap = M.fromList [
                             ((getLabel b, getLabel b'), opener memoized b b') |
                             b <- dfs bdd1 ,
                             b' <- dfs bdd2
                             ]
        opener f (Leaf b _) (Leaf b' _) = b==b'
        opener f (Leaf _ _) (Internal _ _ _ _) = False
        opener f (Internal _ _ _ _) (Leaf _ _) = False
        opener f (Internal v _ l r) (Internal v' _ l' r') = v == v' && f l l' && f r r'


-- | Input : A binary de cision diagram
--   Output: [[][][]] where all bdd in the same list have
--           the same order
getSubBDDBByOrder :: (Ord a, Eq lb) =>
                     ROBDD a lb ->
                     [[ROBDD a lb]]
getSubBDDBByOrder bdd =
  reverse $ sortBy compare (foldr helper [] bdds)
  where bdds = dfs bdd
        --helper :: ROBDD a lb -> [[ROBDD a lb]] -> [[ROBDD a lb]]
        helper bdd [] = [[bdd]]
        helper bdd (x:xs)
          | compare bdd (head x) == EQ = (bdd:x):xs
          | otherwise = x:(helper bdd xs)


-- | Checks if any two bdds in a list are isomorphic
anyIsomorphicQ :: (Ord a, Ord lb) =>
                  [ROBDD a lb] ->
                  Bool
anyIsomorphicQ bdds =
  any (\x -> any (isomorphicQ x) (delete x bdds)) bdds


-- | Checks if in a list there is any node with the
--   right child equal to the left child
--   NOTE: Will return an error when the input has leafs
anyHasEqualChildrenQ :: (Eq a, Eq lb) =>
                        [ROBDD a lb] ->
                        Bool
anyHasEqualChildrenQ list = any (\x -> left x == right x) list

-- | Removes any duplicates by isomorphism
filterIsomorphic :: (Ord a, Ord lb) =>
                    [ROBDD a lb] ->
                    [ROBDD a lb]
filterIsomorphic bdd =
  helper [] bdd
  where helper bdds [] = bdds
        helper bdds (x:xs)
          | any (isomorphicQ x) bdds = helper bdds xs
          | otherwise                = helper (x:bdds) xs


-- | Input : A list of BDD
--   Output : A map from label to that node isomorphic replacement
--   Note: Not to be exported
createMapToIsoReplacement :: (Ord a, Ord lb) =>
                             [ROBDD a lb] ->
                             M.Map lb (ROBDD a lb)
createMapToIsoReplacement list =
  M.fromList [(getLabel b, firstIsomorphic b) | b <- list]
  where firstIsomorphic b = head $ dropWhile (not . isomorphicQ b) laux
        laux = filterIsomorphic list

-- | Input: A list of nodes
--   Output: A mapping to the replacement of such nodes
--           when the children are the same.
--           When a node has two different left children then
--           that node is its own replacement
createMapToChildReplacement :: (Ord a, Ord lb) =>
                               [ROBDD a lb] ->
                               M.Map lb (ROBDD a lb)
createMapToChildReplacement list =
  M.fromList [(getLabel b, replacement b) | b <- list]
  where replacement b
          | left b == right b = left b
          | otherwise = b


-- | Input: A Map with changes to be applied and a list of
--          lists with binary decision diagrams
--   Output: A Map with changes to be applied that results
--           from successively propagating the changes upward
--   NOTE: this function is using unsafe look ups
propagateChanges :: (Ord a, Ord lb) =>
                    M.Map lb (ROBDD a lb) ->
                    [[ROBDD a lb]] ->
                    M.Map lb (ROBDD a lb)
propagateChanges m [] = m
propagateChanges m (x:xs) =
  propagateChanges (foldr helper m x) xs
  where helper :: (Ord a, Ord lb) => ROBDD a lb -> M.Map lb (ROBDD a lb) -> M.Map lb (ROBDD a lb)
        helper (Leaf _ _) _ = undefined
        helper (Internal v lbl l r) dic
          | getLabel l `elem` k && getLabel r `elem` k =
              M.insert lbl (Internal v lbl (dic M.! (getLabel l)) (dic M.! (getLabel r))) dic
          | getLabel l `elem` k =
              M.insert lbl (Internal v lbl (dic M.! (getLabel l)) r) dic
          | getLabel r `elem` k =
              M.insert lbl (Internal v lbl l (dic M.! (getLabel r))) dic
          | otherwise = dic
          where k = M.keys dic

-- | Input: An ordered list f lists of bdd, i.e, [[bdd], [bdd]]
-- | Return: The reduced binary decision diagram resulting from propagating
--           all the changes upward
--   NOTE: This is not safe for stupid inputs, for example
--              * Two binary decision diagrams in the last list
--              * A first list with leafs
--              * Binary decision diagrams in the same list that are connected
--   we do not work on the case were we replace isonodes and
--   nodes with the same children at the same time.
--   this makes propagating the changes much easier.
--   NOTE: After propagating we still need to deal with the case where the  first
--         node in the BDD is directed at two leafs. We can deal with this case
--         just by testing with ==
reduceFromList :: (Ord a, Ord lb) =>
                  [[ROBDD a lb]] ->
                  ROBDD a lb
reduceFromList [x] =
  if l == r
     then r
     else b
  where l = left b
        r = right b
        b = head x
reduceFromList l@(x:xs)
  | null x =
      reduceFromList xs
  | isLeaf (head x) && length x > 2 =
      reduceFromList (map (nub . mapMaybe (applyChange proisoChanges)) l)
  | isLeaf (head x) && length x <= 2 =
      reduceFromList xs
  | not (anyHasEqualChildrenQ x) && not (anyIsomorphicQ x) =
      reduceFromList xs
  | anyIsomorphicQ x =
      reduceFromList (map (nub . mapMaybe (applyChange proisoChanges)) l) --without nub an infinite loop may happen
  | anyHasEqualChildrenQ x =
      reduceFromList (map (nub . mapMaybe (applyChange prochildChanges)) l)
  | otherwise = reduceFromList (map (nub . mapMaybe (applyChange prochildChanges)) l)
  where applyChange m x' = if getLabel x' `elem` M.keys m
                           then if isLeaf (m M.! (getLabel x')) then Nothing else Just $ m M.! (getLabel x')
                           else Just x'
        childChanges = createMapToChildReplacement x
        prochildChanges = propagateChanges childChanges xs
        isoChanges = createMapToIsoReplacement x
        proisoChanges = propagateChanges isoChanges xs
        leafsChange = createMapToIsoReplacement x --we use the map for iso replacement
        -- because if there is more than one leaf then it must be the case that more
        -- than one are isomorphic
        proleafsChange = propagateChanges leafsChange xs


-- | Input: A binary decision Diagram
--   Output : A reduced ordered binary decision diagram
reduce :: (Ord lb, Ord a) =>
          ROBDD a lb ->
          ROBDD a lb
reduce leaf@(Leaf _ _) = leaf
reduce bdd             = reduceFromList $ getSubBDDBByOrder bdd


-- -----------------------------------------------------------------------------
-- END: Algorithms on ROBDD
-- -----------------------------------------------------------------------------



-- -----------------------------------------------------------------------------
-- BEGIN: Interactions with the boolean function package
-- -----------------------------------------------------------------------------

-- -----------------------------------------------------------------------------
-- END: Interact with the bolean function package
-- -----------------------------------------------------------------------------


-- -----------------------------------------------------------------------------
-- BEGIN: Getters for bdds2
-- -----------------------------------------------------------------------------
getChildren :: ROBDD a lb -> [ROBDD a lb]
getChildren (Leaf _ _)         = []
getChildren (Internal _ _ l r) = [l, r]

getLabel :: ROBDD a lb -> lb
getLabel n@(Internal _ _ _ _) = label n
getLabel (Leaf _ l)           = l
-- -----------------------------------------------------------------------------
-- END: Getters for bdds2
-- -----------------------------------------------------------------------------



-- -----------------------------------------------------------------------------
-- Test instances
-- -----------------------------------------------------------------------------
bdd1 = Internal {value = "x2", label = 1, left = t, right =f }
bdd2 = Internal {value = "x1", label = 2, left = t, right = bdd1}


-- This nodes are to test the reduce algorithm
t = Leaf True (-1)
f = Leaf False (-2)
n6 = Internal "x3" 1 (f) (f)
n5 = Internal "x3" 2 (t) f
n4 = Internal "x3" 3 (t) (t)
n3 = Internal "x2" 4 n6 n6
n2 = Internal "x2" 5 n5 n4
n1 = Internal "x1" 6 n3 n2

-- to show that one reduce might not be enough
bddRed2 = Internal "x2" 3 t t
bddRed3 = Internal "x2" 2 t t
bddRed1 = Internal "x1" 1 bddRed2 bddRed3
-- End of reduce tests

-- examples from the book
r5 = Leaf False "R5"
r6 = Leaf True "R6"
s4 = Leaf False "S4"
s5 = Leaf True "S5"
r4 = Internal "x4" "R4" r5 r6
r3 = Internal "x3" "R3" r4 r6
r2 = Internal "x2" "R2" r4 r3
r1 = Internal  "x1" "R1" r2 r3

s3 = Internal "x4" "S3" s4 s5
s2 = Internal "x3" "S2" s3 s5
s1 = Internal  "x1" "S1" s3 s2
-- end examples from the book
