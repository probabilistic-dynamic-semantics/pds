{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

{-|
Module      : Framework.Lambda.Signature
Description : Signatures for constants used across the framework.
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com

Signatures for constants used across the framework.
-}

module Framework.Lambda.Signature ( mkStackSig
                                  , mkStateSig
                                  , tau0
                                  , tauArithmetic
                                  , tauIndicesInit
                                  , tauLogical
                                  , tauProbProg
                                  , tauReals
                                  , tauStatesInit
                                  ) where

import Framework.Lambda.Convenience
import Framework.Lambda.Terms
import Framework.Lambda.Types

-- ** Signatures

-- | Combined signature.
tau0 :: Sig
tau0 = tauArithmetic  <||>
       tauIndicesInit <||>
       tauLogical     <||>
       tauProbProg    <||>
       tauReals       <||>
       tauStatesInit

-- | Some arithmetic operators.
tauArithmetic :: Sig
tauArithmetic = \case
  Left "mult" -> Just (r :× r :→ r)
  Left "add"  -> Just (r :× r :→ r)
  Left "max"  -> Just ((r :→ t) :→ r)
  Left "neg"  -> Just (r :→ r)
  Left "(≥)"  -> Just (r :→ r :→ t)
  _           -> Nothing

-- | Initial indices.
tauIndicesInit :: Sig
tauIndicesInit = \case
  Left "@" -> Just σ -- Blank starting world.
  _        -> Nothing

-- | Logical constants and operators defind thereon.
tauLogical :: Sig
tauLogical = \case
  Left "∀"            -> Just ((α :→ t) :→ t)
  Left "∃"            -> Just ((α :→ t) :→ t)
  Left "(∧)"          -> Just (t :→ t :→ t)
  Left "(∨)"          -> Just (t :→ t :→ t)
  Left "(⇒)"          -> Just (t :→ t :→ t)
  Left "¬"            -> Just (t :→ t)
  Left "T"            -> Just t
  Left "F"            -> Just t
  Left "if_then_else" -> Just (t :× α :× α :→ α)
  Left "(=)"          -> Just (α :× α :→ t)
  _                   -> Nothing

-- | Various useful probability distributions and operators defined thereon.
tauProbProg :: Sig
tauProbProg = \case
  Left "Bernoulli"    -> Just (r :→ P t)
  Left "Beta"         -> Just (r :× r :→ P r)
  Left "disj"         -> Just (r :× P α :× P α :→ P α)
  Left "Normal"       -> Just (r :× r :→ P r)
  Left "Normal_cdf"   -> Just (r :× r :→ r :→ r)
  Left "Logit_normal" -> Just (r :× r :→ P r)
  Left "observe"      -> Just (t :→ P Unit)
  Left "factor"       -> Just (r :→ P Unit)
  Left "Truncate"     -> Just (r :× r :→ P r :→ P r)
  Left "#"            -> Just (P α) -- The undefined distribution.
  Left "𝟙"            -> Just (t :→ r)
  Left "𝔼"            -> Just ((α :→ r) :→ P α :→ r)
  Left "Pr"           -> Just (P t :→ r)
  _                   -> Nothing

-- | Real numbers.
tauReals :: Sig
tauReals = \case
  Right _ -> Just r
  _       -> Nothing

-- | Initial states.
tauStatesInit :: Sig
tauStatesInit = \case
  Left "ϵ" -> Just σ -- Blank starting state.
  _        -> Nothing 


-- * Functions for generating signatures

-- | Make signatures for updating and accessing states.
mkStateSig :: Type -> [(String, Type)] -> Sig
mkStateSig _   []               = const Nothing
mkStateSig sTy ((c, ty) : ctys) = ctySig <||> mkStateSig sTy ctys
  where ctySig :: Sig
        ctySig = \case
          Left c' | c' == c           -> Just (sTy :→ ty)
          Left c' | c' == "upd_" ++ c -> Just (ty :→ sTy :→ sTy)
          _                           -> Nothing

-- | Make signatures for pushing to and popping from stacks.
mkStackSig :: Type -> (Type -> Type) -> (Type -> Type) -> [(String, Type)] -> Sig
mkStackSig _   _ _ []               = const Nothing
mkStackSig sTy f g ((c, ty) : ctys) = ctySig <||> mkStackSig sTy f g ctys
  where ctySig :: Sig
        ctySig = \case
          Left c' | c' == "push_" ++ c -> Just (ty :→ sTy :→ f sTy)
          Left c' | c' == "pop_"  ++ c -> Just (sTy :→ ty :× g sTy)
          _                            -> Nothing
