module DTLFormula
  (
    LocalFormula
  , Formula
  , GlobalFormula
  , localSubFormulas
  , globalSubFormulas
  , closureFormula
  , negateFormula
  , subFormulasAgent
  , findInDepthForAgent
  , psiTest
  ) where

-- TODO: Corrigir recursivamente a profundidade das fórmulas

import           Data.Maybe
import qualified Data.Set   as Set

type PropSymbol = String
type Agent = Int

data LocalFormula = PropositionalSymbol PropSymbol
                  | Implies LocalFormula LocalFormula
                  | Next LocalFormula
                  | Globally LocalFormula
                  | Comunicates Agent LocalFormula
                  | Not LocalFormula
                    deriving (Eq, Ord)

data GlobalFormula = Local Agent LocalFormula
                   | GNot GlobalFormula
                   | GImplies GlobalFormula GlobalFormula
                     deriving (Eq, Ord)

data Formula = FromGlobal GlobalFormula | FromLocal LocalFormula deriving (Eq, Ord)

-- Instancing my custom show for the formulas
instance Show LocalFormula
  where show (PropositionalSymbol a) = show a
        show (Implies a b)           = show a ++ " => " ++ show b
        show (Next a)                = "X(" ++ show a ++ ")"
        show (Globally a)            = "G(" ++ show a ++ ")"
        show (Comunicates agent a)   = "c_" ++ show agent ++ "(" ++ show a ++ ")"
        show (Not a)                 = "~(" ++ show a ++ ")"

instance Show GlobalFormula
  where show (Local agent a) = "@_" ++ show agent ++ "[" ++ show a ++ "]"
        show (GNot a)        = "~(" ++ show a ++ ")"
        show (GImplies a b)  = show a ++ " => " ++ show b

instance Show Formula
  where show (FromLocal a)  = show a
        show (FromGlobal a) = show a



{-|
  Given any global formula and the number of agents
  'closureFormula' returns the closure of the formula
-}
closureFormula :: GlobalFormula -> Int -> Set.Set Formula
closureFormula a n =
  Set.union (Set.map negateFormula s) s
  where s = Set.union w g
        w = Set.fromList $ concatMap (subFormulasAgent a) [1..n]
        g = Set.fromList $ map FromGlobal (globalSubFormulas a)

{-| Given any formula 'negateFormula' negates it-}
negateFormula :: Formula -> Formula
negateFormula (FromLocal (Not f))   = FromLocal f
negateFormula (FromGlobal (GNot a)) = FromGlobal a
negateFormula (FromLocal f)         = FromLocal (Not f)
negateFormula (FromGlobal a)        = FromGlobal (GNot a)

{-|
  The 'subFormulasAgent' functions returns all the subformulas
  that are in the domain of a given agent
-}
subFormulasAgent :: GlobalFormula -> Agent -> [Formula]
subFormulasAgent (Local i1 f) i2    = if i1 == i2
                                         then map FromLocal (localSubFormulas f i1)
                                         else concatMap ( map FromLocal . (`localSubFormulas` i2) . fromJust) (filter isJust (findInDepthForAgent f i2))
subFormulasAgent (GNot f) i         = subFormulasAgent f i
subFormulasAgent (GImplies f1 f2) i = subFormulasAgent f1 i ++ subFormulasAgent f2 i

{-|
  'localSubFormulas' receives a local formula and an agent. It returns all the
  local formulas that are in the domain of said agent.
  When it finds a communication formula it searches in depth for formulas of that
  agent.
-}
localSubFormulas :: LocalFormula -> Agent -> [LocalFormula]
localSubFormulas (PropositionalSymbol s) _ = [PropositionalSymbol s]
localSubFormulas y@(Implies f g)         i = y : localSubFormulas f i ++ localSubFormulas g i
localSubFormulas y@(Next f)              i = y : localSubFormulas f i
localSubFormulas y@(Globally f)          i = y : localSubFormulas f i
localSubFormulas y@(Comunicates _ f)     i = y : concatMap ((`localSubFormulas` i) . fromJust) (filter isJust (findInDepthForAgent f i))
localSubFormulas y@(Not f)               i = y : localSubFormulas f i

{-|
  'findInDepthForAgent' receives an agent and a formula. It searches util it finds
  a formula that communicats with said agent.
-}
findInDepthForAgent :: LocalFormula -> Agent -> [Maybe LocalFormula]
findInDepthForAgent (PropositionalSymbol _) _ = [Nothing]
findInDepthForAgent (Comunicates i1 g) i2     = if i1 == i2
                                                   then [Just g]
                                                   else findInDepthForAgent g i2
findInDepthForAgent (Implies f1 f2) i         = findInDepthForAgent f1 i ++ findInDepthForAgent f2 i
findInDepthForAgent (Not f) i                 = findInDepthForAgent f i
findInDepthForAgent (Next f) i                = findInDepthForAgent f i
findInDepthForAgent (Globally f) i            = findInDepthForAgent f i

{-|
  'globalSubFormulas' breaks down a global formula in all its sub formulas.
-}
globalSubFormulas :: GlobalFormula -> [GlobalFormula]
globalSubFormulas a@(Local _ _)    = [a]
globalSubFormulas a@(GNot f)       = a : globalSubFormulas f
globalSubFormulas a@(GImplies f g) = a : globalSubFormulas f ++ globalSubFormulas g

psiTest :: LocalFormula
psiTest = Implies (Globally (PropositionalSymbol "p") ) (Comunicates 2 (PropositionalSymbol "q"))
psi1 :: LocalFormula
psi1 = Not (PropositionalSymbol "q")
psi2 :: LocalFormula
psi2 = Next $ Not (PropositionalSymbol "q")
psi3 :: LocalFormula
psi3 = Implies psi1 psi2
psiGTest :: GlobalFormula
psiGTest = GNot (Local 1 psiTest)

psiTeseLocal1 = Not (Comunicates 2 (Next (Comunicates 1 (Globally (PropositionalSymbol "p")))))
psiTeseLocal2 = Not (Next (PropositionalSymbol "q"))
psiTeseGlobal = GImplies (Local 1 psiTeseLocal1) (Local 2 psiTeseLocal2)
