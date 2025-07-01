{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

{-|
Module      : Analysis.Factivity.Signature
Description : Signature for factivity.
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com

Signature for factivity.
-}

module Analysis.Factivity.Signature ( tauFact
                                    ) where

import Framework.Lambda.Convenience
import Framework.Lambda.Signature
import Framework.Lambda.Terms
import Framework.Lambda.Types
import Theory.Signature

tauFact :: Sig
tauFact = tau0                                       <||>
          tauNames                                   <||>
          tauStates                                  <||>
          mkStateSig ι [ ("epi", e :→ (ω :→ t) :→ t)
                       , ("ling", e :→ t)
                       , ("phil", e :→ t) ]          <||>
          mkStateSig σ [ ("tau_know", t) ]

tauNames :: Sig
tauNames = \case
  Left "j" -> Just e
  Left "b" -> Just e
  _        -> Nothing
