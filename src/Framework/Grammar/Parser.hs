{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-|
Module      : Framework.Grammar.Parser
Description : CCG parsing, CKY-style (ish).
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com

CKY-style parsing for CCG.
-}

module Framework.Grammar.Parser ( forParse
                                , interpret
                                , interpretations
                                , ParseAs(..)
                                ) where

import           Control.Monad
import           Control.Monad.State
import           Data.List
import qualified Data.Map              as Map
import           Data.Maybe                           (maybeToList)
import           Framework.Grammar.CCG
import           Framework.Lambda
import           Prelude               as Prel hiding (Word)

--------------------------------------------------------------------------------
-- * Interface-agnostic CCG parsing

-- | Chart indices are expressions, and chart elements are sets of parses
-- (@[m]@).
type Chart m = StateT (Map.Map Expr [m]) [] ()

-- | CKY-style CCG expression interpreter, but with parses cached by substring
-- identity instead of by span, for stronger memoization.
interpret :: forall p m. Interpretation p m => Int -> Expr -> Chart m
interpret lex = \case
  -- | Cache each lexical item (but only if needed).
  [w] -> cacheIfNeeded [w] $ do
    m <- get
    let lexSet = (lexica @p !! lex) w
    put (Map.insert [w] lexSet m)
  -- | Cache a complex expression (but only if needed).
  e   -> cacheIfNeeded e $ do
    n <- lift [1 .. length e - 1]
    let (e1, e2) = splitAt n e
    interpret @p lex e1
    interpret @p lex e2
    m <- get
    let i1    = join (maybeToList (Map.lookup e1 m))
        i2    = join (maybeToList (Map.lookup e2 m))
        i3tmp = do i1' <- i1
                   i2' <- i2
                   combineR @p i1' i2' ++ combineL @p i1' i2'
        i3    = join (maybeToList (Map.lookup e m)) ++ i3tmp 
    put (Map.insert e i3 m)
  where cacheIfNeeded :: Expr -> Chart m -> Chart m
        cacheIfNeeded e chart = do m <- get
                                   case Map.lookup e m of
                                     Just _  -> pure ()
                                     Nothing -> chart

newtype ParseAs a = ParseAs { getList :: [a] } deriving Functor

forParse :: ([a] -> [b]) -> ParseAs a -> ParseAs b
forParse f = ParseAs . f . getList

instance Show a => Show (ParseAs a) where
  show (ParseAs []) = ""
  show (ParseAs (a:as)) = show (ParseAs as) ++ "\n" ++
                          show (length (a:as)) ++ ". " ++ show a 

interpretations :: forall p m. (Interpretation p m, Eq m)
                => Expr -> Int -> ParseAs m
interpretations e lex = ParseAs (nub $ join $
                                    map (join . maybeToList . Map.lookup e)
                                    (execStateT (interpret @p lex e) Map.empty)
                                   )
