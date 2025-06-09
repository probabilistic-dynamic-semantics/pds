{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}

{-|
Module      : Grammar.CCG
Description : CCG derivations.
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com

CCG types are defined and used to type strings, analogously to the way λ-terms
are typed.
-}

module Grammar.CCG where

import           Data.Bifunctor
import           Data.List
import           Data.Maybe                         (maybeToList)
import           Control.Monad
import           Control.Monad.State
import qualified Data.Map            as Map
import           Prelude             as Prel hiding (Word)
import           Lambda                             (Typed)

--------------------------------------------------------------------------------
-- * Expressions and grammatical categories

type Word = String
type Expr = [Word]

data Cat = AP | Deg | NP | N | S | Qdeg
         | Cat :/: Cat
         | Cat :\: Cat
  deriving (Eq)

instance Show Cat where
  show = \case
    AP      -> "ap"
    Deg     -> "deg"
    NP      -> "np"
    N       -> "n"
    S       -> "s"
    Qdeg    -> "qDeg"
    a :/: b -> "(" ++ show a ++ "/" ++ show b ++ ")"
    a :\: b -> "(" ++ show a ++ "\\" ++ show b ++ ")"

infixl :/:
infixl :\:

type Lexicon m = Word -> [m]

data Project = Adjectives | Factivity

class Interpretation (p :: Project) m where
  lexica   :: [Lexicon m]
  combineR :: m -> m -> [m]
  combineL :: m -> m -> [m] 
