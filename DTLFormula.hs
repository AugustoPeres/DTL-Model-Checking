module DTLFormula
  (
    LocalFormula
  , Formula
  , localSubFormulas
  , globalSubFormulas
  , GlobalFormula
  , psiTest
  ) where

type PropSymbol = String
type Agent = Int

data LocalFormula = PropositionalSymbol PropSymbol
                  | Implies LocalFormula LocalFormula
                  | Next LocalFormula
                  | Globally LocalFormula
                  | Comunicates Agent LocalFormula
                  | Not LocalFormula
                    deriving (Show, Eq)

data GlobalFormula = Local Agent LocalFormula
                   | GNot GlobalFormula
                   | GImplies GlobalFormula GlobalFormula
                     deriving (Show, Eq)

data Formula = FromLocal LocalFormula | FromGLobal GlobalFormula deriving (Show)

subFormulasAgent :: GlobalFormula -> Agent -> [Formula]
subFormulasAgent alpha i =
  map FromLocal a2
  where a2 = concatMap localSubFormulas a
        a = map (getLocalFormulaAtDepth1 i) aux
        aux = filter (isFormulaOfAgentAtDepth1 i) aux2
        aux2 = globalSubFormulas alpha

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
psiGTest :: GlobalFormula
psiGTest = GNot (Local 1 psiTest)
