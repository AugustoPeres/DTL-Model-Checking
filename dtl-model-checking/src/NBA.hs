module NBA
  (
  NBA
  ) where

import qualified Automaton       as GNBA
import           CommonTypes
import           Data.List       (nub)
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
    Map.foldrWithKey (\k x b -> b ++ showTransitions k) "" d
    where d = delta a
          showTransitions k =
            unlines $ map
                      (\x->show k ++ "->" ++ show(snd x) ++ "[label=\"" ++ show(fst x) ++ "\"];")
                      (fromMaybe [] (Map.lookup k d))


-- ---------------------------------------------------------------------
-- Transformation Functions : These functions are used to tranform
--                            some given automaton. They always return
--                            some new automaton resulting for applying
--                            said transformation.
--
--                            For example deleting or adding a state.
-- ---------------------------------------------------------------------

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
--   We compute strongly connected components and remove all nodes
--   that have no path into a SCC containing final states.
isNeverAcceptingStateQ :: NBA a -> -- ^ Automaton
                          State -> -- ^ State querried
                          Bool
isNeverAcceptingStateQ a s = undefined

-- | Returns true if there is path from the first state
--   to the second state in the given automaton.
existsPathBetweenQ :: NBA a -> -- ^ Automaton
                      State -> -- ^ Departure State
                      State -> -- ^ Arrival State
                      Bool
existsPathBetweenQ a q q' = undefined

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
