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
tauStates = mkStateSig σ                    [ ( "CG"  , P ι ) ]         <||>
            mkStackSig σ (q ι α) (popQ ι α) [ ( "QUD" , α :→ ι :→ t ) ]
