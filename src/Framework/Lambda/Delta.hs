{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

{-|
Module      : Theory.Delta
Description : Delta rules.
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com

Delta rules are defined. These encode algebraic laws relating λ-terms that
feature constants.
-}

module Framework.Lambda.Delta where

import Data.List
import Framework.Lambda.Convenience
import Framework.Lambda.Terms

--------------------------------------------------------------------------------
-- * Delta rules

-- ** Example rules

-- | Performs some arithmetic simplifications.
arithmetic :: DeltaRule
arithmetic = \case
  Add t u      -> case t of
                    Zero -> Just u
                    x@(DCon _) -> case u of
                                    Zero       -> Just x
                                    y@(DCon _) -> Just (x + y)
                                    _          -> Nothing
                    t'         -> case u of
                                    Zero -> Just t'
                                    _    -> Nothing
  Mult t u     -> case t of
                     Zero       -> Just Zero
                     One        -> Just u
                     x@(DCon _) -> case u of
                                     Zero       -> Just Zero
                                     One        -> Just x
                                     y@(DCon _) -> Just (x * y)
                     t'         -> case u of
                                     Zero -> Just Zero
                                     One  -> Just t'
                                     _    -> Nothing
  Neg (DCon x) -> Just (dCon (-x))
  _            -> Nothing

-- | Get rid of vacuous let-bindings.
cleanUp :: DeltaRule
cleanUp = \case
  Let v m k | sampleOnly m && v `notElem` freeVars k -> Just k
  _                                                  -> Nothing

-- | Marginalizes out certain distributions; some other stuff.
disjunctions :: DeltaRule
disjunctions = \case
  Let  b (Bern x)     k                  -> Just (Disj x
                                                  (subst b Tr k) (subst b Fa k)
                                                 )
  Let  v (Disj x m n) k                  -> Just (Disj x
                                                  (Let v m k) (Let v n k)
                                                 )
  Disj _ m            n         | m == n -> Just m
  Disj _ m            Undefined          -> Just m
  Disj _ Undefined    n                  -> Just n
  _                                      -> Nothing

-- | Computes syntactic equalities.
equality :: DeltaRule
equality = \case
  Eq x y | x == y -> Just Tr
  _               -> Nothing

-- | Computes the indicator function.
indicator :: DeltaRule
indicator = \case
  Indi Tr -> Just 1
  Indi Fa -> Just 0
  _       -> Nothing

-- | Computes /if then else/.
ite :: DeltaRule
ite = \case
  ITE Tr x y -> Just x
  ITE Fa x y -> Just y
  _          -> Nothing

logical :: DeltaRule
logical = \case
  And p  Tr -> Just p
  And Tr p  -> Just p
  And Fa _  -> Just Fa
  And _  Fa -> Just Fa
  Or  p  Fa -> Just p
  Or  Fa p  -> Just p
  Or  Tr _  -> Just Tr
  Or  _  Tr -> Just Tr
  _         -> Nothing

-- | Computes the /max/ function.
maxes :: DeltaRule
maxes = \case
   Max (Lam y (GE x (Var y'))) | y' == y -> Just x
   _                                     -> Nothing          

-- | Observing @Tr@ is trivial, while observing @Fa@ yields an undefined
-- probability distribution.
observations :: DeltaRule
observations = \case
  Let _ (Observe Tr) k -> Just k
  Let _ (Observe Fa) _ -> Just Undefined
  _                    -> Nothing

-- | Computes probabilities for certain probabilitic programs.
probabilities :: DeltaRule
probabilities = \case
  Pr (Return Tr)                                             -> Just 1
  Pr (Return Fa)                                             -> Just 0
  Pr (Bern x)                                                -> Just x
  Pr (Disj x t u)                                            -> Just (x * Pr t + (1 - x) * Pr u)
  Pr (Let v (Normal x y) (Return (GE t (Var v')))) | v' == v -> Just (NormalCDF x y t)
  Pr (Let v (Normal x y) (Return (GE (Var v') t))) | v' == v -> Just (NormalCDF x y (- t))
  _                                                          -> Nothing

-- | Computes functions on indices and states. These include reading and writing
-- to locations of fixed type, as well as pushing to and popping from stacks,
-- thus possibly modifying the type of the state.
states :: DeltaRule
states = \case
  LkUp c   (Upd  c' v _) | c' == c -> Just v
  LkUp c   (Upd  c' _ s) | c' /= c -> Just (LkUp c s)
  Upd  c v (Upd  c' _ s) | c' == c -> Just (Upd c v s)
  Pop  c   (Push c' v s) | c' == c -> Just (v & s)
  Pop  c   (Push c' v s) | c' /= c -> Just (v' & s')
    where v', s' :: Term
          v' = Pi1 (Pop c s)
          s' = Push c' v (Pi2 (Pop c s))
  LkUp c   (Push _  _ s)           -> Just (LkUp c s)
  Pop  c   (Upd  c' v s)           -> Just (v' & s')
    where v', s' :: Term
          v' = Pi1 (Pop c s)
          s' = Upd c' v (Pi2 (Pop c s))
  _                                -> Nothing
