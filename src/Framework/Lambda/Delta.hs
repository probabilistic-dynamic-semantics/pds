{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

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

import Control.Monad (guard)
import Data.List
import Data.Ratio
import Framework.Lambda.Convenience
import Framework.Lambda.Delta.Arithmetic
import Framework.Lambda.Terms
import Framework.Lambda.Types

--------------------------------------------------------------------------------
-- * Delta rules

-- ** Example rules

-- | Simplify arithmetic expressions.
arithmetic :: forall simplifier . Arithmetic simplifier => DeltaRule
arithmetic t = do x <- toSimplifier @simplifier t
                  result <- fromSimplifier @simplifier t x
                  guard (result /= t)
                  pure result

cleanUp :: DeltaRule
cleanUp = \case
  Let v m k | isDistr m && v `notElem` freeVars k -> Just k
  _                                               -> Nothing

-- | Marginalizes out certain distributions; some other stuff.
disjunctions :: DeltaRule
disjunctions = \case
  Let  b (Bern x)     k                     -> Just (Disj x
                                                     (subst b Tr k)
                                                     (subst b Fa k)
                                                    )
  Let  v (Disj x m n) k                     -> Just (Disj x
                                                     (Let v m k)
                                                     (Let v n k)
                                                    )
  Disj x (Let v m k) (Let v' n k') | m == n -> Just (Let v'' m (
                                                        Disj x
                                                          (subst v (Var v'') k)
                                                          (subst v' (Var v'') k')
                                                        )
                                                    )
    where v'':_ = fresh [x, k, k']
  Disj x (Let v (Factor y) t) u             -> Just (factor z (Disj ((x * y) / z) (subst v TT t) u))
    where z = x * y + (1 - x)
  Disj x t (Let v (Factor y) u)             -> Just (factor z (Disj (x / z) t (subst v TT u)))
    where z = x + (1 - x) * y
  Disj x m            n            | m == n -> Just m
  Disj x m            Undefined             -> Just (factor x m)
  Disj x Undefined    n                     -> Just (factor (1 - x) n)
  _                                         -> Nothing

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

-- | Compute integrals.
integration :: DeltaRule
integration = \case
  Integrate t (Lam _ x@(DCon _)) | isDistr t -> Just x
  Integrate t (Lam v (Var v'))   | v' == v   -> case t of
                                                  LogitNormal 0 1 -> Just (DCon 0.5)
                                                  Normal x _      -> Just x
                                                  _               -> Nothing
  _                                          -> Nothing

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
   Max (Lam y (GE x (Var y'))) | y' == y
                               , y `notElem` freeVars x -> Just x
   _                                                    -> Nothing          

-- | Observing @Tr@ is trivial, while observing @Fa@ yields an undefined
-- probability distribution.
observations :: DeltaRule
observations = \case
  Let v (Observe Tr) k -> Just (AsMeasure (subst v TT k))
  Let _ (Observe Fa) _ -> Just Undefined
  _                    -> Nothing

-- | Computes probabilities.
probabilities :: DeltaRule
probabilities = \case
  Pr t -> Just (TrueMass t / Mass t)
  _    -> Nothing

-- | Compute masses.
masses :: DeltaRule
masses = \case
  Mass (Return _)                  -> Just 1
  Mass (Let v (Factor (Div (DCon 1) (Mass t))) t')
    | t' == t
    , v `notElem` freeVars t'      -> Just 1
  Mass (Let v t u) | isDistr t     -> Just (Integrate t (Lam v (Mass u)))
  Mass t           | isDistr t     -> Just 1
  Mass (Let v (Factor x) t)        -> Just (x * Mass (subst v TT t))
  Mass (Disj x t u)                -> Just (x * Mass t + (1 - x) * Mass u)
  Mass Undefined                   -> Just 0
  Mass (AsMeasure m)               -> Just (Mass m)
  Mass (Normalize _)               -> Just 1
  Mass (Let v m (AsMeasure k))     -> Just (Mass (Let v m k))
  TrueMass (Return Tr)             -> Just 1
  TrueMass (Return Fa)             -> Just 0
  TrueMass (Let v (Factor x) t)    -> Just (x * TrueMass (subst v TT t))
  TrueMass (Disj x t u)            -> Just (x * TrueMass t + (1 - x) * TrueMass u)
  TrueMass (
    Let v (Normal x y) (
        Return (t `GE` Var v')
        )
    ) | v' == v                    -> Just (NormalCDF x y t)
  TrueMass (
    Let v (Normal x y) (
        Return (Var v' `GE` t)
        )
    ) | v' == v                    -> Just (NormalCCDF x y t)

  TrueMass Undefined               -> Just 0
  TrueMass (AsMeasure m)           -> Just (TrueMass m)
  TrueMass (Normalize m)           -> Just (TrueMass m / Mass m)

  Mass (Let v (Normalize m) k)     -> Just (Mass (Let v m k) / Mass m)

  TrueMass (Let v (Normalize m) k) -> Just (TrueMass (Let v m k) / Mass m)
  TrueMass (Let v m (AsMeasure k)) -> Just (TrueMass (Let v m k))
  _                                -> Nothing

-- | Computes functions on indices and states. These include reading and writing
-- to locations of fixed type, as well as pushing to and popping from stacks,
-- thus possibly modifying the type of the state.
states :: DeltaRule
states = \case
  LkUp c (Upd  c' v _)   | c' == c    -> Just v
  LkUp c (Upd  c' _ s)   | c' /= c    -> Just (LkUp c s)
  Upd  c v (Upd  c' _ s) | c' == c    -> Just (Upd c v s)
  Upd  c (LkUp c' s ) s' | c' == c
                         , s' == s    -> Just s
  Pop  c (Push c' v s)   | c' == c    -> Just (v & s)
  Pop  c (Push c' v s)   | c' /= c    -> Just (v' & s')
    where v', s' :: Term
          v' = Pi1 (Pop c s)
          s' = Push c' v (Pi2 (Pop c s))
  LkUp c   (Push _  _ s)              -> Just (LkUp c s)
  Pop  c   (Upd  c' v s)              -> Just (v' & s')
    where v', s' :: Term
          v' = Pi1 (Pop c s)
          s' = Upd c' v (Pi2 (Pop c s))
  _                                   -> Nothing

factors :: DeltaRule
factors = \case
  Let v (Factor x) (Let v' (Factor y) t) -> Just (Let v (Factor (x * subst v TT y)) (subst v' TT t))
  Let v t (Let v' (Factor x) u)
    | v `notElem` freeVars x             -> Just (Let v' (Factor x) (Let v t u))
  Let v (Factor One) t                   -> Just (subst v TT t)
  Let v t (Let v' (Factor (Var v'')) u)
    | v'' == v && v `notElem` freeVars u -> Just (Let v' (Factor (mean t)) u)
  Normalize (Let v (Factor (DCon c)) k)
    | c > 0 -> Just (Normalize (subst v TT k))
  _                                      -> Nothing

measureTracking :: DeltaRule
measureTracking = \case
  Let v m (AsMeasure k)   -> Just (AsMeasure (Let v m k))
  Normalize (AsMeasure m) -> Just (Normalize m)
  _                       -> Nothing

normalization :: Sig -> DeltaRule
normalization tau = \case
  Normalize m | Just (P _) <- typeOf (ty tau m) -> Just m
  _                                             -> Nothing
