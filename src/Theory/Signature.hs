{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

{-|
Module      : Theory.Signature
Description : Signatures
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com

Convenience functions, smart constructors, etc.
-}

module Theory.Signature where

import Framework.Lambda.Convenience
import Framework.Lambda.Terms
import Framework.Lambda.Types

-- ** Signatures

-- | An example signature.
tau :: Sig
tau = \case
  Left  "∀"            -> Just ((α :→ t) :→ t)
  Left  "∃"            -> Just ((α :→ t) :→ t)
  Left  "(∧)"          -> Just (t :→ t :→ t)
  Left  "(∨)"          -> Just (t :→ t :→ t)
  Left  "(⇒)"          -> Just (t :→ t :→ t)
  Left  "¬"            -> Just (t :→ t)
  Left  "T"            -> Just t
  Left  "F"            -> Just t
  Left  "if_then_else" -> Just (t :→ α :× α :→ α)
  Left  "(=)"          -> Just (α :× α :→ t)
  Left  "@"            -> Just ι -- Blank starting world.
  Left  "ϵ"            -> Just σ -- Blank starting state.
  Left  "upd_ling"     -> Just ((e :→ t) :→ ι :→ ι)
  Left  "ling"         -> Just (ι :→ e :→ t)
  Left  "phil"         -> Just (ι :→ e :→ t)
  Left  "upd_soc_pla"  -> Just ((e :→ t) :→ ι :→ ι)
  Left  "soc_pla"      -> Just (ι :→ e :→ t)
  Left  "sleep"        -> Just (ι :→ e :→ t)
  Left  "like"         -> Just (ι :→ e :→ e :→ t)
  Left  "love"         -> Just (ι :→ e :→ e :→ t)
  Left  "j"            -> Just e
  Left  "b"            -> Just e
  Left  "Bernoulli"    -> Just (r :→ P t)
  Left  "Beta"         -> Just (r :× r :→ P r)
  Left  "Normal"       -> Just (r :× r :→ P r)
  Left  "Normal_cdf"   -> Just (r :× r :→ r :→ r)
  Left  "LogitNormal"  -> Just (r :× r :→ P r)
  Left  "Truncate"     -> Just (r :× r :→ P r :→ P r)
  Left  "upd_height"   -> Just ((e :→ r) :→ ι :→ ι)
  Left  "height"       -> Just (ι :→ e :→ r)
  Left  "upd_d_tall"   -> Just (r :→ σ :→ σ)
  Left  "d_tall"       -> Just (σ :→ r)
  Left  "(≥)"          -> Just (r :→ r :→ t)
  Left  "disj"         -> Just (r :→ P α :× P α :→ P α)
  Left  "mult"         -> Just (r :× r :→ r)
  Left  "add"          -> Just (r :× r :→ r)
  Left  "neg"          -> Just (r :→ r)
  Left  "#"            -> Just (P α)
  Left  "𝟙"            -> Just (t :→ r)
  Left  "𝔼"            -> Just ((α :→ r) :→ P α :→ r)
  Left  "Pr"           -> Just (P t :→ r)
  Left  "factor"       -> Just (r :→ P Unit)
  Left  "observe"      -> Just (t :→ P Unit)
  Left  "upd_tau_know" -> Just (t :→ σ :→ σ)
  Left  "tau_know"     -> Just (σ :→ t)
  Left  "upd_CG"       -> Just (P ι :→ σ :→ σ)
  Left  "CG"           -> Just (σ :→ P ι)
  Left  "upd_QUD"      -> Just ((κ :→ ι :→ t) :→ σ :→ q ι κ σ)
  Left  "QUD"          -> Just (q ι κ σ :→ κ :→ ι :→ t)
  Left  "upd_epi"      -> Just ((e :→ (ω :→ t) :→ t) :→ ι :→ ι)
  Left  "epi"          -> Just (ι :→ e :→ (ω :→ t) :→ t)
  Left  "max"          -> Just ((r :→ t) :→ r)
  Left  "σ"            -> Just r
  Left  _              -> Nothing
  Right _              -> Just r
