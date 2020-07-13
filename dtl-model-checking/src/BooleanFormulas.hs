module BooleanFormulas (BooleanFormula, varAppearsNegated,
                        andFromList, orFromList, getVariables,)

where

-- -----------------------------------------------------------------------------
-- BEGIN: Definition of the boolean function data type
-- -----------------------------------------------------------------------------

data BooleanFormula a =Atom a
                      | Neg (BooleanFormula a)
                      | Or (BooleanFormula a) (BooleanFormula a)
                      | And (BooleanFormula a) (BooleanFormula a)
                      deriving (Eq, Ord)

-- Important instances
instance (Show a) => Show (BooleanFormula a) where
  show (Atom a)    = show a
  show (Neg f)     = "~" ++ show f
  show (Or f1 f2)  = "( " ++ show f1 ++ " )\\/ ( " ++ show f2 ++ " )"
  show (And f1 f2) = "( " ++ show f1 ++ " )/\\( " ++ show f2 ++ " )"
-- -----------------------------------------------------------------------------
-- END: Definition of the boolean function data type
-- -----------------------------------------------------------------------------

-- -----------------------------------------------------------------------------
-- BEGIN: Creating formulas
-- -----------------------------------------------------------------------------
andFromList :: [(Bool, a)] -> BooleanFormula a
andFromList []     = undefined
andFromList (x:xs) =
  foldr helper (start x) xs
  where helper a b = if fst a then And (Atom $ snd a) b else And (Neg (Atom $ snd a)) b
        start a = (if fst a then Atom $ snd a else Neg (Atom $ snd a))


orFromList :: [a] -> BooleanFormula a
orFromList []     = undefined
orFromList (x:xs) = foldr (\b y -> And (Atom b) y) (Atom x) xs
-- -----------------------------------------------------------------------------
-- END: Creating formulas
-- -----------------------------------------------------------------------------

-- -----------------------------------------------------------------------------
-- BEGIN: Getters for clauses
-- -----------------------------------------------------------------------------
getVariables :: BooleanFormula a -> [a]
getVariables f =
  helper f []
  where helper (Atom a) q  = a:q
        helper (Neg f') q   = helper f' q
        helper (Or f' g) q  = helper f' q ++ helper g q
        helper (And f' g) q = helper f' q ++ helper g q


varAppearsNegated :: Eq a => a -> BooleanFormula a -> Bool
varAppearsNegated _ (Atom _) = False
varAppearsNegated a (Neg f) = if f == Atom a then True else varAppearsNegated a f
varAppearsNegated a (Or f g) = varAppearsNegated a f || varAppearsNegated a g
varAppearsNegated a (And f g) = varAppearsNegated a f || varAppearsNegated a g
-- -----------------------------------------------------------------------------
-- END: Getters for clauses
-- -----------------------------------------------------------------------------





-- Some example variables
x1 = Atom "x1"
x2 = Atom "x2"
x3 = Atom "x2"
fTese = Or (x1 `And` x2) (x1 `And` Neg x3)
