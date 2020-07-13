{-# OPTIONS_GHC -O2               #-}
module NBA
  (
  NBA(..), State, getNeighbours, getNeighboursGeneral, deleteNeverAcceptingStates,
  empty, addState, addInitialState, addFinalState, addTransition, compressAlphaBalls,
  getAlphaBalls, getNeverAcceptingStates, fullSimplify
  ) where



import           CommonTypes
import           Control.Monad   (replicateM)
import           Data.List       (intersect, nub, permutations, sort,
                                  subsequences, union, (\\))
import qualified Data.Map.Strict as Map
import           Data.Maybe
import qualified Data.Set        as Set


-- This module contains the revelant function to manipulate NBA

-- This is more general because (NBA a) allows for any type of alphabet
-- symbols. Where previously we were limited to
--         type AlphabetSymbol = (Set.Set Formula, Action)
-- Maybe should derive some instaces of a.

type State = Int
data NBA a = NBA { states        :: [State],
                   inicialStates :: [State],
                   finalStates   :: [State],
                   delta         :: Map.Map State [(a, State)] -- transtion function
                 } deriving (Show)

-- Printing the automaton in a more user user friendly fashion
instance Show a => FiniteGraphRepresentable (NBA a) where
  -- TODO: Falta meter aqui as restantes coisas que fazem o graphciz file
  toGraphviz a =
    "digraph finite_state_machine {\n" ++
    "node[shape=doublecircle width=2 height=2 fontsize=50];" ++ foldr (\a b -> b ++ " " ++ show a ++ ";") "" f ++ "\n" ++
    "edge[decorate=1 minlen=2];\nnode[width=2 height=2 fontsize=50 shape=circle]\n" ++
    Map.foldrWithKey (\k x b -> b ++ showTransitions k) "" d ++
    "}"
    where f = finalStates a
          d = delta a
          showTransitions k =
            unlines $ map
                      (\x->show k ++ "->" ++ show(snd x) ++ "[label=\"" ++ show(fst x) ++ "\"];")
                      (fromMaybe [] (Map.lookup k d))


-- This data types are used for the complementation algorithm
type LevelRanking = Map.Map State Int -- We represent _|_ as -1


-- this is just an empty automaton
empty :: NBA a
empty = NBA [] [] [] Map.empty
-- ---------------------------------------------------------------------
-- Transformation Functions : These functions are used to tranform
--                            some given automaton. They always return
--                            some new automaton resulting for applying
--                            said transformation.
--
--                            For example deleting or adding a state.
-- ---------------------------------------------------------------------

-- | Just adds a new state to the automaton
addState :: NBA a -> State -> NBA a
addState nba s =
  NBA (states nba `union` [s])
      (inicialStates nba)
      (finalStates nba)
      (delta nba)


-- | Adds a new initial state to the automaton
addInitialState :: NBA a -> State -> NBA a
addInitialState nba s =
  NBA (states nba `union` [s])
      (inicialStates nba `union` [s])
      (finalStates nba)
      (delta nba)


-- | Adds a new final state to the automaton
addFinalState :: NBA a -> State -> NBA a
addFinalState nba s =
  NBA (states nba `union` [s])
      (inicialStates nba)
      (finalStates nba `union` [s])
      (delta nba)


-- | Adds a new transition
addTransition :: (Eq a) =>
                 NBA a ->
                 State-> -- departure state
                 a -> -- propositional letter responsible
                 State-> -- arrival state
                 NBA a
addTransition nba s sigma s' =
  NBA (states nba)
      (inicialStates nba)
      (finalStates nba)
      (Map.insert s newTransition d)
  where newTransition = (fromMaybe [] ((d Map.!? s))) `union` [(sigma, s')]
        d = delta nba



-- | This function reverses the automaton. Meaning that all
--   arrows will be reversed.
--   Returns the new reversed automaton
transpose :: NBA a -> NBA a
transpose a =
  NBA {states = s, inicialStates = i, finalStates = f, delta = d'}
  where s  = states a
        i  = inicialStates a
        f  = finalStates a
        d  = delta a
        d' = Map.fromList [(k, helper k) | k<-s]
        helper key = Map.foldrWithKey (\k a b -> b ++ map (helper2 k) (filter (\x->snd x==key) a)) [] d
        helper2 key (a,_)=(a,key)

-- | Deletes a list of states from the automaton
--   NOTE: After the application of this function we are left
--         with an automaton that has, for example, states = [1, 3,4].
--         Therefore later we will need a function to normalize this automaton.
deleteStates :: NBA a ->
                [State] -> -- ^ List with the states to be deleted
                NBA a -- ^ New automaton
deleteStates a st =
  NBA {states=s, inicialStates=i, finalStates=f, delta=d''}
  where s   = states a \\ st
        i   = inicialStates a \\ st
        f   = finalStates a \\ st
        d   = delta a
        d'  = Map.filterWithKey (\k _ -> k `notElem` st) d
        d'' = Map.map (filter (\x->snd x `notElem` st)) d'

-- | This function normalizes the keys in the automaton
normalize :: NBA a -> NBA a
normalize = undefined

-- | Finds the never accepting states using the getter function
--   (getNeverAcceptingStates) and removes them from the automaton
deleteNeverAcceptingStates :: NBA a -> -- ^ Automaton
                              NBA a    -- ^ Automaton without states
deleteNeverAcceptingStates a = deleteStates a (getNeverAcceptingStates a)

-- | Finds all the alpha balls and compresses them
compressAlphaBalls :: Eq a => NBA a -> NBA a
compressAlphaBalls a =
  deleteStates NBA {states=s, inicialStates=i, finalStates=newFinalStates, delta=d'} delstates
  where alphaBalls     = getAlphaBalls a
        delstates      = concatMap tail alphaBalls
        newFinalStates = map head alphaBalls `union` finalStates a
        alphaStates    = concat alphaBalls
        s = states a
        i = inicialStates a
        d' = Map.mapWithKey
             (\k y -> if k `elem` alphaStates then map (\(x, _) -> (x, k)) y else y)
             d
        d  = delta a

-- | Receives an automaton and fully compresses it using alpha balls
--   and never accepting states.
fullSimplify :: Eq a => NBA a -> NBA a
fullSimplify = compressAlphaBalls . deleteNeverAcceptingStates

-- ---------------------------------------------------------------------
-- End of transformation functions
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Query functions: These functions are used to answer True or False
--                  about the state of the automaton.
-- ---------------------------------------------------------------------

-- | Returns true if a node is never accepting.
--   We say that a node is never accepting iff there is no
--   accepting run leading from it.
--   We compute all strongly connected components and then
--   remove all nodes that don't have a path leading into a
--   SCC that has a final state.
isNeverAcceptingStateQ :: NBA a -> -- ^ Automaton
                          State -> -- ^ State querried
                          Bool
isNeverAcceptingStateQ a s =
  not $ any (existsPathBetweenQ a s) sccf
  where sccf = concat $ filter (any (`elem` f)) (kosaraju a) -- scc with final states
        f    = finalStates a

-- | Returns true if there is path from the first state
--   to the second state in the given automaton.
existsPathBetweenQ :: NBA a -> -- ^ Automaton
                      State -> -- ^ Departure State
                      State -> -- ^ Arrival State
                      Bool
existsPathBetweenQ a q q' = q' `elem` dfs a [q] [] False

-- | Returns true iff there is a path from an inicial state to
--   the querried state in the given automaton.
isReachableQ :: NBA a -> -- ^ Automaton
                State -> -- ^ State we want to querry
                Bool
isReachableQ a s =
  any (\x -> existsPathBetweenQ a x s) iStates
  where iStates = inicialStates a

-- | Returns true if the given state is dead.
--   We say that a state is dead iff there are no outgoing edges
--   from that state
--   NOTE: This function will return true if we give it a state that is not
--         in the automaton.
isDeadStateQ :: NBA a -> -- ^ Automaton
                State -> -- ^ querried state
                Bool
isDeadStateQ a s =
  null $ fromMaybe [] neigs
  where neigs = getNeighbours a s

-- | isAlphaBall returns true if a list of nodes
--   form an alpha ball.
---  NOTE: We are assuming that the input is already a scc
isAlphaBall :: Eq a => NBA a -> [State] -> Bool
isAlphaBall a scc =
  any (`elem` f) scc && -- there is an accepting state
  foldr (\y b -> b && null (nub (map snd (fromMaybe [] (getNeighbours a y))) \\ scc)) True scc && -- there are no transitions leaving
  transitionWithSameLetters a scc -- transition is done under the same letter
  where f       = finalStates a
        d       = delta a



-- | Returns true if all transitions for
--   the states occur under exactly yhe same propositional letters
transitionWithSameLetters :: Eq a => NBA a -> [State] -> Bool
transitionWithSameLetters a scc =
  allEqual letters
  where letters = map (map fst . (\x -> fromMaybe [] (Map.lookup x d))) scc
        d       = delta a
        allEqual []     = True
        allEqual (x:xs) = foldr (\y b -> b && null (y\\x) && null (x\\y)) True xs


-- ---------------------------------------------------------------------
-- End of query functions
-- ---------------------------------------------------------------------


-- ---------------------------------------------------------------------
-- Getters for the automaton: This functions are used to get data
--                            from the automaton.
--                            For example: if we want to return the
--                            the reachable states from some other state
-- ---------------------------------------------------------------------

-- | This function finds all the alpha-balls in the automaton
--   alpha-ball:
--      * Strongly connected component
--      * There is a unique label for the transitions inside the ball
--      * There is no transition leaving the ball
--      * Cotains an accepting state
getAlphaBalls :: Eq a => NBA a -> [[State]]
getAlphaBalls a =
  filter (isAlphaBall a) scc
  where scc = kosaraju a

-- | This function decomposes the automaton in its strongly
--   maximal conected components using the Kosaraju's algorithm
--   NOTE: error on empty automatons
kosaraju :: NBA a ->
            [[State]] -- ^ list with strongly connected maximal conected components
kosaraju a =
  helper ord' [] []
  where ord' =  makeOrder $ dfs a [head s] [] True
        makeOrder ord
          | s == sort ord = ord
          | otherwise = makeOrder ((dfs a [head (s \\ ord)] ord True \\ ord) ++ ord)
        s = sort $ states a
        aT  = transpose a
        helper :: [State] -> [State] -> [[State]] -> [[State]]
        helper order visited scc
          | null order = scc
          | otherwise  = helper (order \\ b) (b ++ visited) (b:scc)
          where b = dfs aT [head order] [] True \\ visited

-- | Given a state returns all its neigbours in a list according to
--   the alphabet symbol that allow it's transition.
--   For example if q0 -p-> q1 then (p, q1) is in the output of
--   getNeighbours a q0
getNeighbours :: NBA a -> -- ^ Automaton
                 State -> -- ^ State
                 Maybe [(a, State)] -- returns nothing if the key is wrong
getNeighbours a s =
  Map.lookup s d
  where d = delta a

-- | INPUT : Automaton a, list of states s and an alphabet letter l
--   RETURNS : Union of all delta(s', l) for all s' in s.
getNeighboursGeneral :: Eq a =>
                        NBA a -> -- ^ Automaton
                        [State] -> -- ^ list of states
                        a -> -- ^ propositional letter
                        [State]
getNeighboursGeneral a s l= -- meter antes list comprehension
  foldr (\x y -> union y [snd w | w <- fromMaybe [] (Map.lookup x d), fst w == l]) [] s
  where d = delta a


-- | Returns all the never accepting states in the automaton
getNeverAcceptingStates :: NBA a -> [State]
getNeverAcceptingStates a = filter (a `isNeverAcceptingStateQ`) (states a)

-- | Given a state computes all the states that can be reached from that
--   state.
--   The function uses a Q to make the visits while tracking the visited states.
--   Thus it should be called as dfs automaton [node] []
--   NOTE: When using n = True on the input the function will assume that "a"
--         reaches "a" even when no self loop exists.
--   NOTE: THIS RETURNS [a] even if a is not on the list of possible node
--         Should make this return Nothing when that happens
dfs :: NBA a -> -- ^ Automaton
       [State] -> -- ^ Q used in the search
       [State] -> -- ^ visited states
       Bool -> -- ^ Varible to decide if a visits a even when no edges are present
       [State]
dfs a [] v _ = v
dfs a (x:xs) v b
  | b = dfs a ([s | s<-neigs, s `notElem` (x:v)]++xs) newvisited True
  | otherwise = dfs a ([s | s<-neigs, s `notElem` v]++xs) v True
  where neigs = map snd (fromMaybe [] (getNeighbours a x))
        newvisited = if x `elem` v then v else v++[x]
-- ---------------------------------------------------------------------
-- End of getters for the automaton
-- ---------------------------------------------------------------------


-- ---------------------------------------------------------------------
-- Complementation of the automaton
-- ---------------------------------------------------------------------

-- | Makes all the level rankings given a certain automaton
makeLevelRankings :: NBA a -> [LevelRanking]
makeLevelRankings a =
  [Map.fromList (zip q i) | q<-[s], i<-replicateM n [-1..2*n],
                            all (\x -> (even (i!!x) || (i!!x) == -1) || (q!!x) `notElem` f) [0..(n-1)]]
  where s = states a
        n = length s
        f = finalStates a

-- | Checks if level ranking g1 covers level ranking g2 for a given automaton a
--   DEFINITION: g' covers g if for all q and q': g(q) >= 0 and q' \in delta(q) implies
--               0 <= g'(q') <= g(q)
covers :: NBA a ->        -- ^ Automaton
          LevelRanking -> -- ^ g1
          LevelRanking -> -- ^ g2
          Bool
covers a g' g =
  all condition s
  where s = states a
        d = delta a
        condition q = let aux1 = fromJust $ Map.lookup q g
                      in all (\x ->
                             aux1 == -1 ||
                             (x `notElem` map snd (fromJust $ Map.lookup q d)) ||
                             (0 <= fromJust (Map.lookup x g') &&  fromJust (Map.lookup x g') <= aux1)
                             )
                          s

-- | Returns the set even as defined in the book
evenLR :: LevelRanking -> [State]
evenLR lr = [k | k <- Map.keys lr, even (fromJust $ Map.lookup k lr)]

-- | This function returns the complementary automaton
complement :: Eq a =>
              NBA a -> -- ^ original automaton
              [a] ->   -- ^ all the alphabet symbols
              NBA a
complement a sigma =
  NBA { states = [1..n'],
        inicialStates = [1],
        finalStates = [1..length f],
        delta = d'
      }
  where sm = Map.fromList $ zip [1..] s' ++ zip [1..] f ++ [(1, (g0, []))]
        s' = [(r, q) | r<-levelRankings, q<-subsequences s]
        f = [(r, [])|r<-levelRankings]
        s = states a
        g0 = Map.fromList ([(s, 2*n) | s<-q0] ++ [(s, -1) | s<-s\\q0])
        q0 = inicialStates a
        n = length s
        n' = length s'
        levelRankings = makeLevelRankings a
        d = delta  a
        d' = Map.fromList
            [(q, helper (fromJust $ Map.lookup q sm)) | q<-[1..n']]
        --helper :: Eq a1 => (LevelRanking, [State]) -> [(a1, State)]
        helper q@(lr, set)
          | null set  = [(pl, q') | pl<-sigma, q'<-[1..n'],
                                    let query = fromJust (Map.lookup q' sm),
                                    covers a (fst query) lr,
                                    null (snd query \\ evenLR (fst query)) && null (evenLR (fst query) \\ snd query)
                                   ]
          | otherwise = [(pl, q') | q'<-[1..n'],
                                    let query = fromJust (Map.lookup q' sm),
                                    pl<-sigma,
                                    let neig  = getNeighboursGeneral a set pl,
                                    covers a (fst query) lr,
                                    null ((snd query `intersect` neig) \\ evenLR (fst query)) && null (evenLR (fst query) \\ (snd query `intersect` neig))
                                    ]
-- ---------------------------------------------------------------------
-- End of complementation of the automaton
-- ---------------------------------------------------------------------

-- -----------------------------------------------------------------
-- Test automatons and other variables
-- -----------------------------------------------------------------
-- gsmall = NBA { states = [1, 2],
--                finalStates = [2],
--                inicialStates = [1],
--                delta = Map.fromList [(1, [("a", 1), ("b", 1), ("b", 2)]),
--                                      (2, [("b", 2)])]
--               }

-- g = NBA { states = [1, 2, 3],
--           finalStates = [1],
--           inicialStates = [1, 2],
--           delta = Map.fromList [(1, [("a", 1), ("b", 2), ("a", 3)]) , (2, [("b", 1), ("a", 3)]), (3, [])]
--         }

-- g2 = NBA { states = [1, 2, 3, 4],
--            finalStates = [1, 4],
--            inicialStates = [1, 2],
--            delta = Map.fromList [(1, [("a", 1), ("b", 2), ("a", 3)]),
--                                  (2, [("b", 1), ("a", 3), ("a", 4)]),
--                                  (3, [("b", 2), ("c", 4)]),
--                                  (4, [("", 4)])]
--         }

-- g3 = NBA {
--            states = [1, 2, 3, 4, 5],
--            finalStates = [3, 4, 5],
--            inicialStates = [2, 1],
--            delta = Map.fromList [ (1, [("", 2), ("", 4)]),
--                                   (2, [("", 3)]),
--                                   (3, [("", 1)]),
--                                   (4, [("", 5)]),
--                                   (5, [("", 4)])
--                                 ]
--          }

-- gAlphaBall = NBA {
--            states = [1, 2, 3, 4, 5],
--            finalStates = [2, 4],
--            inicialStates = [],
--            delta = Map.fromList [ (1, [("", 2)]),
--                                   (2, [("", 3)]),
--                                   (3, [("", 1)]),
--                                   (4, [("a", 5)]),
--                                   (5, [("a", 4)])
--                                 ]
--          }

-- gAlphaBall2 = NBA {
--            states = [1, 2, 3, 4, 5],
--            finalStates = [2, 4],
--            inicialStates = [],
--            delta = Map.fromList [ (1, [("", 4)]),
--                                   (2, [("", 3)]),
--                                   (3, [("", 1)]),
--                                   (4, [("a", 5)]),
--                                   (5, [("a", 4)])
--                                 ]
--          }

-- gTesteComponents = NBA {
--                          states = [0..13],
--                          finalStates = [1, 7, 13, 0, 6],
--                          inicialStates = [],
--                          delta = Map.fromList [ (0, [("", 0), ("", 0)]),
--                                                 (1, [("", 2), ("", 8)]),
--                                                 (2, [("", 0)]),
--                                                 (3, [("", 2), ("", 4), ("", 7)]),
--                                                 (4, [("", 6)]),
--                                                 (5, [("", 4)]),
--                                                 (6, [("", 5)]),
--                                                 (7, [("", 8), ("", 10), ("", 12)]),
--                                                 (8, [("", 11)]),
--                                                 (9, [("", 7)]),
--                                                 (10, [("", 11), ("", 13)]),
--                                                 (11, [("", 9)]),
--                                                 (12, [("a", 13), ("", 13)]),
--                                                 (13, [("", 12), ("a", 12)])
--                                               ]
--                        }


-- gBugTransitionSystem = NBA {
--                              states = [1..4],
--                              finalStates = [],
--                              inicialStates = [],
--                              delta = Map.fromList [ (1, []),
--                                                     (2, []),
--                                                     (3, [("", 4)]),
--                                                     (4, [("", 1)])]
--                            }
