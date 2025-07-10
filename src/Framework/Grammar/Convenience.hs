{-|
Module      : Framework.Grammar.Convenience
Description : Convenience functions
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com

Convenience functions for defining CCG grammars and lexica.
-}

module Framework.Grammar.Convenience where

import Framework.Grammar.CCG

--------------------------------------------------------------------------------
-- * Expressions and grammatical categories

ap, deg, noun, np, qDeg, stnc :: Cat
ap   = Base "ap"
deg  = Base "deg"
noun = Base "n"
np   = Base "np"
qDeg = Base "qDeg"
stnc = Base "s"
