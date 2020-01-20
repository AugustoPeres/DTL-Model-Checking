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
