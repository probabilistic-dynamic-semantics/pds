{-|
Module      : Grammar
Description : Exports CCG operations, lexica, and parsers.
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com
-}

module Grammar ( module Grammar.CCG
               , module Grammar.Lexica.SynSem
               , module Grammar.Parser
               ) where

import Grammar.CCG
import Grammar.Parser
import Grammar.Lexica.SynSem
