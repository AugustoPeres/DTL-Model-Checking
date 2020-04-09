module DTLFormula
  (
    LocalFormula(..)
  , Formula(..)
  , GlobalFormula(..)
  , Agent
  , localSubFormulas
  , globalSubFormulas
  , closureFormula
  , negateFormula
  , subFormulasAgent
  , findInDepthForAgent
  , psiTest
  , isImplication
  , isNegation
  , isNext
  , isGlobally
  , isCommunication
  , isAtAgent
  , isGlobal
  , isLocal
  , isLiteral
  , isPropSymbol
  , tailFormula
  , communicationAgent
  , getSubFormulasImplication
  , PropSymbol
  , wrapGlobal
  , wrapLocal
  ) where

import           Data.Maybe
import qualified Data.Set   as Set

type PropSymbol = String
type Agent = Int

data LocalFormula = PropositionalSymbol PropSymbol
                  | Not LocalFormula
                  | Next LocalFormula
                  | Globally LocalFormula
                  | Comunicates Agent LocalFormula
                  | Implies LocalFormula LocalFormula
                    deriving (Eq, Ord)

data GlobalFormula = Local Agent LocalFormula
                   | GNot GlobalFormula
                   | GImplies GlobalFormula GlobalFormula
                     deriving (Eq, Ord)

data Formula = FromLocal LocalFormula | FromGlobal GlobalFormula deriving (Eq, Ord)

-- Instancing my custom show for the formulas
instance Show LocalFormula
  where show (PropositionalSymbol a) = a -- no need to use show since this is already a string
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

-- Wraps a local formula
wrapLocal :: LocalFormula -> Formula
wrapLocal f = FromLocal f

-- Wraps a local formula
wrapGlobal :: GlobalFormula -> Formula
wrapGlobal f = FromGlobal f



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

{-|
  Checks if a formula is an implication
-}
isImplication :: Formula -> Bool
isImplication (FromLocal (Implies _ _))   = True
isImplication (FromGlobal (GImplies _ _)) = True
isImplication _                           = False

isNegation :: Formula -> Bool
isNegation (FromLocal (Not _))   = True
isNegation (FromGlobal (GNot _)) = True
isNegation _                     = False

isGlobally :: Formula -> Bool
isGlobally (FromLocal (Globally _)) = True
isGlobally _                        = False

isNext :: Formula -> Bool
isNext (FromLocal (Next _)) = True
isNext _                    = False

isCommunication :: Formula -> Bool
isCommunication (FromLocal (Comunicates _ _)) = True
isCommunication _                             = False

isAtAgent :: Formula -> Agent -> Bool
isAtAgent (FromGlobal (Local i' _)) i = i == i'
isAtAgent _ _                         = False

isGlobal :: Formula -> Bool
isGlobal (FromGlobal _) = True
isGlobal _              = False

isLocal :: Formula -> Bool
isLocal f = not $ isGlobal f

isPropSymbol :: Formula -> Bool
isPropSymbol (FromLocal (PropositionalSymbol _)) = True
isPropSymbol _                                   = False

isLiteral :: Formula -> Bool
isLiteral (FromLocal (Not psi)) = isPropSymbol (FromLocal psi)
isLiteral g@_                   = isPropSymbol g

tailFormula :: Formula -> Formula -- returns the tail of a formula
tailFormula (FromLocal (Implies _ _))           = undefined
tailFormula (FromGlobal (GImplies _ _))         = undefined
tailFormula (FromLocal (PropositionalSymbol _)) = undefined
tailFormula (FromLocal (Next f))                = FromLocal f
tailFormula (FromLocal (Globally f))            = FromLocal f
tailFormula (FromLocal (Not f))                 = FromLocal f
tailFormula (FromLocal (Comunicates _ f))       = FromLocal f
tailFormula (FromGlobal (Local _ f))            = FromLocal f
tailFormula (FromGlobal (GNot f))               = FromGlobal f

-- returns the agent with which we comunicate
communicationAgent :: Formula -> Agent
communicationAgent (FromLocal (Comunicates i _)) = i
communicationAgent _                             = undefined

-- | receives a formula psi1 => psi2 and returns
--   [psi1, psi2].
getSubFormulasImplication :: Formula -> [Formula]
getSubFormulasImplication (FromLocal (Implies f1 f2))   = [FromLocal f1, FromLocal f2]
getSubFormulasImplication (FromGlobal (GImplies f1 f2)) = [FromGlobal f1, FromGlobal f2]
getSubFormulasImplication _ = undefined

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
