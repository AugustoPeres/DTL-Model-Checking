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
  , isOr
  , isAnd
  , isNegation
  , isNext
  , isDualX
  , isGlobally
  , isEventually
  , isCommunication
  , isDualCom
  , isAtAgent
  , isAtSomeAgent
  , isGlobal
  , isLocal
  , isLiteral
  , isPropSymbol
  , tailFormula
  , communicationAgent
  , dualComAgent
  , localAgent
  , getSubFormulasImplication
  , getSubFormulasOr
  , getSubFormulasAnd
  , PropSymbol
  , wrapGlobal
  , wrapLocal
  , makeNNF
  , negateGlobalFormula
  , majorationPTH
  ) where

import           Data.Maybe
import qualified Data.Set   as Set

type PropSymbol = String
type Agent = Int

data LocalFormula = PropositionalSymbol PropSymbol
                  | Not LocalFormula
                  | And LocalFormula LocalFormula
                  | Or LocalFormula LocalFormula
                  | Next LocalFormula
                  | N LocalFormula
                  | Globally LocalFormula
                  | Eventually LocalFormula
                  | Comunicates Agent LocalFormula
                  | DualCom Agent LocalFormula
                  | Implies LocalFormula LocalFormula
                    deriving (Eq, Ord, Read)

data GlobalFormula = Local Agent LocalFormula
                   | GNot GlobalFormula
                   | GAnd GlobalFormula GlobalFormula
                   | GOr GlobalFormula GlobalFormula
                   | GImplies GlobalFormula GlobalFormula
                     deriving (Eq, Ord, Read)

data Formula = FromLocal LocalFormula | FromGlobal GlobalFormula deriving (Eq, Ord)

-- Instancing my custom show for the formulas
instance Show LocalFormula
  where show (PropositionalSymbol a) = a -- no need to use show since this is already a string
        show (Implies a b)           = show a ++ " => " ++ show b
        show (Next a)                = "X(" ++ show a ++ ")"
        show (N a)                   = "N(" ++ show a ++ ")"
        show (And a b)               = show a ++ "/\\" ++ show b
        show (Or a b)                = show a ++ "\\/" ++ show b
        show (Globally a)            = "G(" ++ show a ++ ")"
        show (Eventually f)          = "F(" ++ show f ++ ")"
        show (Comunicates agent a)   = "c_" ++ show agent ++ "(" ++ show a ++ ")"
        show (DualCom agent a)       = "xx_" ++ show agent ++ "(" ++ show a ++ ")"
        show (Not a)                 = "~(" ++ show a ++ ")"

instance Show GlobalFormula
  where show (Local agent a) = "@_" ++ show agent ++ "[" ++ show a ++ "]"
        show (GNot a)        = "~(" ++ show a ++ ")"
        show (GAnd a b)      = show a ++ "/\\" ++ show b
        show (GOr a b)       = show a ++ "\\/" ++ show b
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


negateGlobalFormula :: GlobalFormula -> GlobalFormula
negateGlobalFormula (GNot f) = f
negateGlobalFormula f        = GNot f


negateLocalFormula :: LocalFormula -> LocalFormula
negateLocalFormula (Not f) = f
negateLocalFormula f       = Not f

-- | Input: A DTL GlobalFormula
--   Output: That formula in NNF i.e, with negations only at the level
--           of the propositional symbols.
makeNNF :: GlobalFormula -> GlobalFormula
makeNNF (Local i f)             = Local i (makeNNFlocal f)
makeNNF (GNot (Local i f))      = makeNNF (Local i (negateLocalFormula f))
makeNNF (GAnd f1 f2)            = GAnd (makeNNF f1) (makeNNF f2)
makeNNF (GOr f1 f2)             = GOr (makeNNF f1) (makeNNF f2)
makeNNF (GNot (GAnd f1 f2))     = GOr (makeNNF (negateGlobalFormula f1)) (makeNNF (negateGlobalFormula f2))
makeNNF (GNot (GOr f1 f2))      = GAnd (makeNNF (negateGlobalFormula f1)) (makeNNF (negateGlobalFormula f2))
makeNNF (GImplies f1 f2)        = GOr (makeNNF (negateGlobalFormula f1)) (makeNNF f2)
makeNNF (GNot (GImplies f1 f2)) = GAnd (makeNNF f1) (makeNNF (negateGlobalFormula f2))


makeNNFlocal :: LocalFormula -> LocalFormula
makeNNFlocal (PropositionalSymbol p) = PropositionalSymbol p
makeNNFlocal (Not (PropositionalSymbol p)) = Not $ PropositionalSymbol p
makeNNFlocal (And f1 f2) = And (makeNNFlocal f1) (makeNNFlocal f2)
makeNNFlocal (Not (And f1 f2)) = Or (makeNNFlocal (negateLocalFormula f1)) (makeNNFlocal (negateLocalFormula f2))
makeNNFlocal (Or f1 f2) = Or (makeNNFlocal f1) (makeNNFlocal f2)
makeNNFlocal (Not (Or f1 f2)) = And (makeNNFlocal (negateLocalFormula f1)) (makeNNFlocal (negateLocalFormula f2))
makeNNFlocal (Next f) = Next (makeNNFlocal f)
makeNNFlocal (Not (Next f)) = N (makeNNFlocal (negateLocalFormula f))
makeNNFlocal (N f) = N (makeNNFlocal f)
makeNNFlocal (Not (N f)) = Next (makeNNFlocal (negateLocalFormula f))
makeNNFlocal (Globally f) = Globally (makeNNFlocal f)
makeNNFlocal (Not (Globally f)) = Eventually (makeNNFlocal (negateLocalFormula f))
makeNNFlocal (Eventually f) = Eventually (makeNNFlocal f)
makeNNFlocal (Not (Eventually f)) = Globally (makeNNFlocal (negateLocalFormula f))
makeNNFlocal (Comunicates i f) = Comunicates i (makeNNFlocal f)
makeNNFlocal (Not (Comunicates i f)) = DualCom i (makeNNFlocal (negateLocalFormula f))
makeNNFlocal (DualCom i f) = DualCom i (makeNNFlocal f)
makeNNFlocal (Not (DualCom i f)) = Comunicates i (makeNNFlocal (negateLocalFormula f))
makeNNFlocal (Implies f1 f2) = Or (makeNNFlocal (negateLocalFormula f1)) (makeNNFlocal f2)
makeNNFlocal (Not (Implies f1 f2)) = And (makeNNFlocal f1) (makeNNFlocal (negateLocalFormula f2))


-- This computes the majoration for a local DTL formula
majorationPTH :: Formula -> Int
majorationPTH f
  | isPropSymbol    f = 0
  | isCommunication f = 1 + majorationPTH (tailFormula f)
  | isDualCom       f = 1 + majorationPTH (tailFormula f)
  | isImplication   f = max (majorationPTH $ subImp!!0) (majorationPTH $ subImp!!1)
  | isOr            f = max (majorationPTH $ subOr!!0) (majorationPTH $ subOr!!1)
  | isAnd           f = max (majorationPTH $ subAnd!!0) (majorationPTH $ subAnd!!1)
  | otherwise         = majorationPTH (tailFormula f)
  where subImp = getSubFormulasImplication f
        subOr  = getSubFormulasOr f
        subAnd = getSubFormulasAnd f


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
subFormulasAgent (GOr _ _)        i = undefined -- leav this undefined
subFormulasAgent (GAnd _ _)       i = undefined


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
localSubFormulas (Or _ _)                _ = undefined --for now we leave this undefined
localSubFormulas (And _ _)               _ = undefined
localSubFormulas (Eventually _)          _ = undefined
localSubFormulas (N _)                   _ = undefined

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
findInDepthForAgent (Or _ _) i                = undefined -- leave this undefined for now
findInDepthForAgent (And _ _) i               = undefined
findInDepthForAgent (Eventually _ ) i         = undefined
findInDepthForAgent (N _) i                   = undefined
findInDepthForAgent (DualCom _ _) i           = undefined

{-|
  'globalSubFormulas' breaks down a global formula in all its sub formulas.
-}
globalSubFormulas :: GlobalFormula -> [GlobalFormula]
globalSubFormulas a@(Local _ _)    = [a]
globalSubFormulas a@(GNot f)       = a : globalSubFormulas f
globalSubFormulas a@(GImplies f g) = a : globalSubFormulas f ++ globalSubFormulas g
globalSubFormulas (GAnd _ _)       = undefined -- we leave this undefined
globalSubFormulas (GOr _ _)        = undefined


{-|
  Checks if a formula is an implication
-}
isImplication :: Formula -> Bool
isImplication (FromLocal (Implies _ _))   = True
isImplication (FromGlobal (GImplies _ _)) = True
isImplication _                           = False

isOr :: Formula -> Bool
isOr (FromLocal (Or _ _))   = True
isOr (FromGlobal (GOr _ _)) = True
isOr _                      = False -- must change this when adding or to the global formulas

isAnd :: Formula -> Bool
isAnd (FromLocal (And _ _))   = True
isAnd (FromGlobal (GAnd _ _)) = True
isAnd _                       = False

isEventually :: Formula -> Bool
isEventually (FromLocal (Eventually _)) = True
isEventually _                          = False

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

isDualX :: Formula -> Bool
isDualX (FromLocal (N _)) = True
isDualX _                 = False

isCommunication :: Formula -> Bool
isCommunication (FromLocal (Comunicates _ _)) = True
isCommunication _                             = False

isDualCom :: Formula -> Bool
isDualCom (FromLocal (DualCom _ _)) = True
isDualCom _                         = False

isAtAgent :: Formula -> Agent -> Bool
isAtAgent (FromGlobal (Local i' _)) i = i == i'
isAtAgent _ _                         = False


isAtSomeAgent :: Formula -> Bool
isAtSomeAgent (FromGlobal (Local _ _)) = True
isAtSomeAgent _                        = False

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
tailFormula (FromLocal (Or _ _))                = undefined
tailFormula (FromLocal (And _ _))               = undefined
tailFormula (FromGlobal (GImplies _ _))         = undefined
tailFormula (FromLocal (PropositionalSymbol _)) = undefined
tailFormula (FromLocal (Next f))                = FromLocal f
tailFormula (FromLocal (N f))                   = FromLocal f
tailFormula (FromLocal (Globally f))            = FromLocal f
tailFormula (FromLocal (Eventually f))          = FromLocal f
tailFormula (FromLocal (Not f))                 = FromLocal f
tailFormula (FromLocal (Comunicates _ f))       = FromLocal f
tailFormula (FromLocal (DualCom _ f))           = FromLocal f
tailFormula (FromGlobal (Local _ f))            = FromLocal f
tailFormula (FromGlobal (GNot f))               = FromGlobal f

-- returns the agent with which we comunicate
communicationAgent :: Formula -> Agent
communicationAgent (FromLocal (Comunicates i _)) = i
communicationAgent _                             = undefined


localAgent :: Formula -> Agent
localAgent (FromGlobal (Local i _)) = i
localAgent _                        = undefined

-- return the communication agent in the dual formula
dualComAgent :: Formula -> Agent
dualComAgent (FromLocal (DualCom i _)) = i
dualComAgent _                         = undefined

-- | receives a formula psi1 => psi2 and returns
--   [psi1, psi2].
getSubFormulasImplication :: Formula -> [Formula]
getSubFormulasImplication (FromLocal (Implies f1 f2))   = [FromLocal f1, FromLocal f2]
getSubFormulasImplication (FromGlobal (GImplies f1 f2)) = [FromGlobal f1, FromGlobal f2]
getSubFormulasImplication _ = undefined


getSubFormulasOr :: Formula -> [Formula]
getSubFormulasOr (FromLocal (Or f1 f2))   = [FromLocal f1, FromLocal f2]
getSubFormulasOr (FromGlobal (GOr f1 f2)) = [FromGlobal f1, FromGlobal f2]
getSubFormulasOr _                        = undefined -- must change here when adding globally


getSubFormulasAnd :: Formula -> [Formula]
getSubFormulasAnd (FromLocal (And f1 f2))   = [FromLocal f1, FromLocal f2]
getSubFormulasAnd (FromGlobal (GAnd f1 f2)) = [FromGlobal f1 , FromGlobal f2]
getSubFormulasAnd _                         = undefined -- must change here when adding globally


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
