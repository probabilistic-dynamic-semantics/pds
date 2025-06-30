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

module Theory.Delta where

import Control.Applicative
import Data.List
import Framework.Lambda.Convenience
import Framework.Lambda.Terms
import Theory.Signature

--------------------------------------------------------------------------------
-- * Delta rules

-- ** Combining rules

(<||>) :: Alternative m => (a -> m b) -> (a -> m b) -> a -> m b
f <||> g = \x -> f x <|> g x

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

-- | Computes functions on indices.
indices :: DeltaRule
indices = \case
  Epi    (UpdEpi p _)    -> Just p
  Epi    (UpdLing _ i)   -> Just (Epi i)
  Epi    (UpdSocPla _ i) -> Just (Epi i)
  Ling   (UpdLing p _)   -> Just p
  Ling   (UpdEpi _ i)    -> Just (Ling i)
  Ling   (UpdSocPla _ i) -> Just (Ling i)
  Height (UpdHeight p _) -> Just p
  Height (UpdSocPla _ i) -> Just (Height i)
  SocPla (UpdSocPla p _) -> Just p
  SocPla (UpdHeight _ i) -> Just (SocPla i)
  SocPla (UpdLing _ i)   -> Just (SocPla i)
  SocPla (UpdEpi _  i)   -> Just (SocPla i)
  _                      -> Nothing

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
  Let _ (Observe Fa) k -> Just Undefined
  _                    -> Nothing

-- | Computes probabilities for certain probabilitic programs.
probabilities :: DeltaRule
probabilities = \case
  Pr (Return Tr)                                             -> Just 1
  Pr (Return Fa)                                             -> Just 0
  Pr (Bern x)                                                -> Just x
  Pr (Disj x t u)                                            -> Just (x * Pr t + (1 - x) * Pr u)
  Pr (Let v (Normal x y) (Return (GE t (Var v')))) | v' == v -> Just (NormalCDF x y t)
  Pr (Let v (Normal x y) (Return (GE (Var v') t))) | v' == v -> Just (NormalCDF (- x) y t)
  _                                                          -> Nothing

-- | Computes functions on states.
states :: DeltaRule
states = \case
  CG      (UpdCG cg _)     -> Just cg
  CG      (UpdDTall _ s)   -> Just (CG s)
  CG      (UpdQUD _ s)     -> Just (CG s)
  CG      (UpdTauKnow _ s) -> Just (CG s)
  DTall   (UpdDTall d _)   -> Just d
  DTall   (UpdCG _ s)      -> Just (DTall s)
  DTall   (UpdQUD _ s)     -> Just (DTall s)
  QUD     (UpdQUD q _)     -> Just q
  QUD     (UpdCG _ s)      -> Just (QUD s)
  QUD     (UpdDTall _ s)   -> Just (QUD s)
  QUD     (UpdTauKnow _ s) -> Just (QUD s)
  TauKnow (UpdTauKnow b _) -> Just b
  TauKnow (UpdCG _ s)      -> Just (TauKnow s)
  TauKnow (UpdQUD _ s)     -> Just (TauKnow s)
  _                        -> Nothing
