{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

{-|
Module      : Analysis.Adjetives.Signature
Description : Signature for gradable adjectives.
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com

Signature for gradbale adjectives.
-}

module Analysis.Adjectives.Signature ( tauAdj
                                     ) where

import Framework.Lambda.Convenience
import Framework.Lambda.Signature
import Framework.Lambda.Terms
import Framework.Lambda.Types
import Theory.Signature

tauAdj :: Sig
tauAdj = tau0                                      <||>
         tauNames                                  <||>
         tauStates                                 <||>
         mkStateSig ι [ ( "soc_pla"   , e :→ t )
                      , ( "ling"      , e :→ t )
                      , ( "phil"      , e :→ t )
                      , ( "height"    , e :→ r )
                      , ( "emptiness" , e :→ r )
                      , ( "d_tall"    , r      )
                      , ( "d_empty"   , r      ) ]

tauNames :: Sig
tauNames = \case
  Left "j" -> mkTy e
  Left "b" -> mkTy e
  _        -> Nothing
