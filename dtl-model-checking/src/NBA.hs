module NBA
  (
  NBA
  ) where

import qualified Automaton       as GNBA
import           CommonTypes
import           Data.List       (nub, (\\))
import qualified Data.Map.Strict as Map
import           Data.Maybe
import qualified Data.Set        as Set


-- This module contains the revelant function to manipulate NBA

-- This is more general because (NBA a) allows for any type of alphabet
-- symbols. Where previously we were limited to
--         type AlphabetSymbol = (Set.Set Formula, Action)
-- Maybe should derive some instaces of a.
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
                      (\x->show k ++ "->" ++ show(snd x) ++ "[label=" ++ show(fst x) ++ "];")
                      (fromMaybe [] (Map.lookup k d))


-- ---------------------------------------------------------------------
-- Transformation Functions : These functions are used to tranform
--                            some given automaton. They always return
--                            some new automaton resulting for applying
--                            said transformation.
--
--                            For example deleting or adding a state.
-- ---------------------------------------------------------------------

-- | This function reverses the automaton. Meaning that all
--   arrows will be reversed.
--   Returns the new reversed automaton
transpose :: NBA a -> NBA a
transpose a =
  NBA {states = s, inicialStates = i, finalStates = f, delta = d'}
  where s = states a
        i = inicialStates a
        f = finalStates a
        d = delta a
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

-- ---------------------------------------------------------------------
-- End of transformation functions
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Query functions: These functions are used to answer True or False
--                  about the state of the automaton.
-- ---------------------------------------------------------------------

-- | This function decomposes the automaton in its strongly
--   maximal conected components using the Kosaraju's algorithm
kosaraju :: NBA a ->
            [[State]] -- ^ list with strongly connected maximal conected components
kosaraju a =
  helper ord [] []
  where ord = dfs a [1] [] True
        aT  = transpose a
        helper :: [State] -> [State] -> [[State]] -> [[State]]
        helper order visited scc
          | null order = scc
          | otherwise  = helper (order \\ b) (b ++ visited) (b:scc)
          where b = dfs aT [head order] [] True \\ visited


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

-- ---------------------------------------------------------------------
-- End of query functions
-- ---------------------------------------------------------------------


-- ---------------------------------------------------------------------
-- Getters for the automaton: This functions are used to get data
--                            from the automaton.
--                            For example: if we want to return the
--                            the reachable states from some other state
-- ---------------------------------------------------------------------

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

-- | Converts a generalized non deterministic Bucgi automaton
--   into a non-deterministic Buchi automaton
toNBA :: GNBA.GNBA -> NBA GNBA.AlphabetSymbol
toNBA g =
  NBA { states = s'',
        inicialStates = q0',
        finalStates = f',
        delta = delta'
      }
  where delta' = Map.fromList [
                                (i, helper (fromJust $ Map.lookup i sm)) | i<-s''
                              ]
        q0' = [i | i<-s'',
                   fst (fromJust (Map.lookup i sm)) `elem` iStates,
                   snd (fromJust (Map.lookup i sm)) == 0
             ]
        f' = [i | i<-s'',
                  fst (fromJust (Map.lookup i sm)) `Set.member` head finalSets,
                  snd (fromJust (Map.lookup i sm)) == 0] ---- note that this will raise an erro if finalSets = []
        sm = Map.fromList  $ zip s'' s'
        -- sm is a mapping {1: (q, k).., n:(q', k')}
        s'' = [1..(length s')]
        s' = [(q, k) | q<-s, k<-[0..(nFinalSets-1)]]
        s = GNBA.states g
        nFinalSets = length finalSets
        finalSets = auxGetter g
        iStates = GNBA.inicialStates g
        d = GNBA.delta g
        auxGetter :: GNBA.GNBA -> [Set.Set State]
        auxGetter g
          | null $ GNBA.finalStates g = [Set.fromList s]
          | otherwise = GNBA.finalStates g
        helper :: (State, Int) -> [(GNBA.AlphabetSymbol, State)]
        helper qi@(q, i)
          | q `Set.member` (finalSets!!i) =
              [(sigma, s) | s<-s'',
                            sigma<-nub $ map fst (fromJust (Map.lookup q d)),
                            (sigma, fst (fromJust (Map.lookup s sm))) `elem` fromJust (Map.lookup q d),
                            snd (fromJust $ Map.lookup s sm) == (i+1) `mod` nFinalSets]
          | otherwise =
              [(sigma, s) | s<-s'',
                            sigma<-nub $ map fst (fromJust (Map.lookup q d)),
                            (sigma, fst (fromJust (Map.lookup s sm))) `elem` fromJust (Map.lookup q d),
                            snd (fromJust $ Map.lookup s sm) == i]




-- -----------------------------------------------------------------
-- Test automatons and other variables
-- -----------------------------------------------------------------
g = NBA { states = [1, 2, 3],
          finalStates = [1],
          inicialStates = [1, 2],
          delta = Map.fromList [(1, [("a", 1), ("b", 2), ("a", 3)]) , (2, [("b", 1), ("a", 3)]), (3, [])]
        }

g2 = NBA { states = [1, 2, 3, 4],
           finalStates = [1, 4],
           inicialStates = [1, 2],
           delta = Map.fromList [(1, [("a", 1), ("b", 2), ("a", 3)]),
                                 (2, [("b", 1), ("a", 3), ("a", 4)]),
                                 (3, [("b", 2), ("c", 4)]),
                                 (4, [("", 4)])]
        }

g3 = NBA {
           states = [1, 2, 3, 4, 5],
           finalStates = [],
           inicialStates = [],
           delta = Map.fromList [ (1, [("", 2), ("", 4)]),
                                  (2, [("", 3)]),
                                  (3, [("", 1)]),
                                  (4, [("", 5)]),
                                  (5, [("", 4)])
                                ]
         }

gTesteComponents = NBA {
                         states = [0..13],
                         finalStates = [1, 7],
                         inicialStates = [],
                         delta = Map.fromList [ (0, [("", 5), ("", 1)]),
                                                (1, [("", 2), ("", 3), ("", 8)]),
                                                (2, [("", 0)]),
                                                (3, [("", 2), ("", 4), ("", 7)]),
                                                (4, [("", 6)]),
                                                (5, [("", 4)]),
                                                (6, [("", 5)]),
                                                (7, [("", 8), ("", 10), ("", 12)]),
                                                (8, [("", 11)]),
                                                (9, [("", 7)]),
                                                (10, [("", 11), ("", 13)]),
                                                (11, [("", 9)]),
                                                (12, [("", 13)]),
                                                (13, [("", 12)])
                                              ]
                       }
