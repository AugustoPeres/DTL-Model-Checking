module DTLFormula
  (
    LocalFormula
  , Formula
  , localSubFormulas
  , globalSubFormulas
  , GlobalFormula
  , psiTest
  ) where

-- TODO: Corrigir recursivamente a profundidade das fórmulas

import qualified Data.Set as Set

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
  Set.union (Set.map negateFormula w ) w
  where w    = Set.union set1 set2
        set1 = Set.fromList $ map FromGlobal (globalSubFormulas a)
        set2 = (helper Set.empty) $ map (Set.fromList . subFormulasAgent a) [1..n]
        helper s [x]    = Set.union s x
        helper s (x:xs) = helper (Set.union s x) xs

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
subFormulasAgent alpha i =
  map FromLocal a2
  where a2 = concatMap localSubFormulas a
        a = map (getLocalFormulaAtDepth1 i) aux
        aux = filter (isFormulaOfAgentAtDepth1 i) aux2
        aux2 = globalSubFormulas alpha

{-|
  'getLocalFormulas' returns all the formulas of the agent i
  at any recursion depth that are inside some GlobalFormula
-}

-- This becomes simpler if we notice that we need only look in formulas
-- with the @ operator (Local)

-- getLocalFormulas :: Agent -> GlobalFormula -> [LocalFormula]
-- getLocalFormulas i a =
--   if isFormulaOfAgentAtDepth1 i a
--     then b : getFormulaOfAgentAtDepth i b
--     else getFormulaOfAgentAtDepth i c
--   where b = getFormulaOfAgentAtDepth i a -- this maybe is undefined, chekc for problems
--         c = getFirstLocalFormula a
--
-- getFirstLocalFormula :: GlobalFormula -> LocalFormula
-- getFirstLocalFormula (Local i a) = a
-- getFirstLocalFormula (GNot a) = getFirstLocalFormula a
-- getForstLocalFormula (GImplies a1 a1) =


{-|
  'isFormulaOfAgentAtDepth' checks if there is a formula in the domain of
  agent i at any depth in a local formula for some other agent j
-}
-- isFormulaOfAgentAtDepth :: Agent -> LocalFormula -> Bool
-- isFormulaOfAgentAtDepth _ (PropositionalSymbol _) = False
-- isFormulaOfAgentAtDepth i (Comunicates i1 f)      = if i1 == i then True else isFormulaOfAgentAtDepth i f
-- isFormulaOfAgentAtDepth i (Implies f1 f2)         = isFormulaOfAgentAtDepth i f1 || isFormulaOfAgentAtDepth i f2
-- isFormulaOfAgentAtDepth i (Next f)                = isFormulaOfAgentAtDepth i f
-- isFormulaOfAgentAtDepth i (Globally f)            = isFormulaOfAgentAtDepth i f
-- isFormulaOfAgentAtDepth i (Not f)                 = isFormulaOfAgentAtDepth i f
--
-- {-|
--   'getFormulaOfAgentAtDepth' returns a list of all formulas for some agent i
--   that are inside some local formula for agent j
-- -}
-- getFormulaOfAgentAtDepth :: Agent -> LocalFormula -> [LocalFormula]
-- getFormulaOfAgentAtDepth _ (PropositionalSymbol _) = []
-- getFormulaOfAgentAtDepth i (Comunicates i1 f)      = if i1 == i then [f] ++ getFormulaOfAgentAtDepth i f else getFormulaOfAgentAtDepth i f
-- getFormulaOfAgentAtDepth i (Implies f1 f2)         = getFormulaOfAgentAtDepth i f1 ++ getFormulaOfAgentAtDepth i f2
-- getFormulaOfAgentAtDepth i (Next f)                = getFormulaOfAgentAtDepth i f
-- getFormulaOfAgentAtDepth i (Globally f)            = getFormulaOfAgentAtDepth i f
-- getFormulaOfAgentAtDepth i (Not f)                 = getFormulaOfAgentAtDepth i f

isFormulaOfAgentAtDepth1 :: Int -> GlobalFormula -> Bool
isFormulaOfAgentAtDepth1 i1 (Local i2 f) = i1 == i2
isFormulaOfAgentAtDepth1 _ _             = False

getLocalFormulaAtDepth1 :: Int -> GlobalFormula -> LocalFormula
getLocalFormulaAtDepth1 i1 (Local i2 f) = if i1 == i2 then f else undefined
getLocalFormulaAtDepth1 _ _             = undefined

localSubFormulas :: LocalFormula -> [LocalFormula]
localSubFormulas (PropositionalSymbol s) = [PropositionalSymbol s]
localSubFormulas y@(Implies f g)         = y : localSubFormulas f ++ localSubFormulas g
localSubFormulas y@(Next f)              = y : localSubFormulas f
localSubFormulas y@(Globally f)          = y : localSubFormulas f
localSubFormulas y@(Comunicates _ _)     = [y] -- this needs to be changed
localSubFormulas y@(Not f)               = y : localSubFormulas f

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
psi3 = Implies (psi1) (psi2)
psiGTest :: GlobalFormula
psiGTest = GNot (Local 1 psiTest)
