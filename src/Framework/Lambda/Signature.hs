{-# LANGUAGE KindSignatures #-}
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
  Left "mult" -> mkTy (r :× r :→ r)
  Left "div"  -> mkTy (r :× r :→ r)
  Left "add"  -> mkTy (r :× r :→ r)
  Left "max"  -> mkTy ((r :→ t) :→ r)
  Left "neg"  -> mkTy (r :→ r)
  Left "(≥)"  -> mkTy (r :→ r :→ t)
  _           -> Nothing

-- | Initial indices.
tauIndicesInit :: Sig
tauIndicesInit = \case
  Left "@" -> mkTy σ -- Blank starting world.
  _        -> Nothing

-- | Logical constants and operators defind thereon.
tauLogical :: Sig
tauLogical = \case
  Left "∀"            -> mkTy ((α :→ t) :→ t)
  Left "∃"            -> mkTy ((α :→ t) :→ t)
  Left "(∧)"          -> mkTy (t :→ t :→ t)
  Left "(∨)"          -> mkTy (t :→ t :→ t)
  Left "(⇒)"          -> mkTy (t :→ t :→ t)
  Left "¬"            -> mkTy (t :→ t)
  Left "T"            -> mkTy t
  Left "F"            -> mkTy t
  Left "if_then_else" -> mkTy (t :× α :× α :→ α)
  Left "(=)"          -> mkTy (α :× α :→ t)
  _                   -> Nothing

-- | Various useful probability distributions and operators defined thereon.
tauProbProg :: Sig
tauProbProg = \case
  Left "Bernoulli"    -> mkTy (r :→ P t)
  Left "Beta"         -> mkTy (r :× r :→ P r)
  Left "Normal"       -> mkTy (r :× r :→ P r)
  Left "Normal_cdf"   -> mkTy (r :× r :→ r :→ r)
  Left "Normal_ccdf"  -> mkTy (r :× r :→ r :→ r)
  Left "Logit_normal" -> mkTy (r :× r :→ P r)
  Left "Uniform"      -> mkTy (r :× r :→ P r)
  Left "disj"         -> mkTy (r :× G α γ :× G β γ :→ G (TyCon "+" [α, β]) γ)
  Left "factor"       -> mkTy (r :→ M Unit)
  Left "observe"      -> mkTy (t :→ M Unit)
  Left "truncate"     -> mkTy (r :× r :→ P r :→ P r)
  Left "#"            -> mkTy (M α) -- The undefined distribution.
  Left "𝟙"            -> mkTy (t :→ r)
  Left "𝔼"            -> mkTy ((α :→ r) :→ P α :→ r)
  Left "pr"           -> mkTy (P t :→ r)
  Left "mass"         -> mkTy (G α β :→ r)
  Left "true_mass"     -> mkTy (G α β :→ r)
  Left "integrate"    -> mkTy (P α :× (α :→ r) :→ r)
  Left "normalize"    -> mkTy (G α β :→ P β)
  Left "as_measure"   -> mkTy (G α β :→ M β)
  _                   -> Nothing

-- | Real numbers.
tauReals :: Sig
tauReals = \case
  Right _ -> mkTy r
  _       -> Nothing

-- | Initial states.
tauStatesInit :: Sig
tauStatesInit = \case
  Left "ϵ" -> mkTy σ -- Blank starting state.
  _        -> Nothing 


-- * Functions for generating signatures

-- | Make signatures for updating and accessing states.
mkStateSig :: Type -> [(String, Type)] -> Sig
mkStateSig _   []               = const Nothing
mkStateSig sTy ((c, ty) : ctys) = ctySig <||> mkStateSig sTy ctys
  where ctySig :: Sig
        ctySig = \case
          Left c' | c' == c           -> mkTy (sTy :→ ty)
          Left c' | c' == "upd_" ++ c -> mkTy (ty :→ sTy :→ sTy)
          _                           -> Nothing

-- | Make signatures for pushing to and popping from stacks.
mkStackSig :: Type -> (Type -> Type) -> (Type -> Type) -> [(String, Type)] -> Sig
mkStackSig _   _ _ []               = const Nothing
mkStackSig sTy f g ((c, ty) : ctys) = ctySig <||> mkStackSig sTy f g ctys
  where ctySig :: Sig
        ctySig = \case
          Left c' | c' == "push_" ++ c -> mkTy (ty :→ sTy :→ f sTy)
          Left c' | c' == "pop_"  ++ c -> mkTy (sTy :→ ty :× g sTy)
          _                            -> Nothing
