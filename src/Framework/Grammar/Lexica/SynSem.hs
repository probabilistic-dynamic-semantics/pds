{-# LANGUAGE LambdaCase #-}

{-|
Module      : Grammar.Lexica.SynSem
Description : Components for defining CCG lexica with catogories and λ-terms.
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com
-}

module Grammar.Lexica.SynSem where

import Grammar.CCG
import Lambda

--------------------------------------------------------------------------------
-- * Lexica with syntax and semantics

-- | A representation for expressions having both a category (@syn@) and a typed
-- λ-term (@sem@).
data SynSem = SynSem { syn :: Cat, sem :: Typed } deriving (Eq, Show)
