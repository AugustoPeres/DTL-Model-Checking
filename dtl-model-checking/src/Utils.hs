module Utils (bernoulli)

where

-- -----------------------------------------------------------------------------
-- Decription: This module contains some functions that come in handy
--             without really fitting in any of the other modules
-- -----------------------------------------------------------------------------

import System.Random

-- | Returns an infinite list resulting from bernoulli trials with
--   probability p. It uses an stdGen to create the array
bernoulli :: StdGen -> Float -> [Bool]
bernoulli gen p = map (<p) ((randoms gen) :: [Float])

