{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

{-|
Module      : Theory.Signature
Description : Theory-level signatures
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com

Theory-level signatures.
-}

module Theory.Signature ( tauStates
                        ) where

import Framework.Lambda.Convenience
import Framework.Lambda.Signature
import Framework.Lambda.Terms
import Framework.Lambda.Types

tauStates :: Sig
tauStates = mkStateSig σ [ ("CG", P ι) ] <||> \case
  Left "QUD"     -> Just (q ι α σ :→ α :→ ι :→ t)
  Left "upd_QUD" -> Just ((α :→ ι :→ t) :→ σ :→ q ι α σ)
  _              -> Nothing
