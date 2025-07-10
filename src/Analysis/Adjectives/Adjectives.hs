{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}

{-|
Module      : Analysis.Adjectives.Adjectives
Description : Adjectives lexicon.
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com
-}

module Analysis.Adjectives.Adjectives where

import Analysis.Adjectives.Signature
import Framework.Grammar.Convenience
import Framework.Grammar.CCG
import Framework.Grammar.Lexica.SynSem
import Framework.Grammar.Lexica.SynSem.Convenience as Convenience
import Framework.Lambda

--------------------------------------------------------------------------------
-- * Lexica for adjectives

instance Indices Adjectives where
  context = [ "d_tall" ]
  world   = [ "height"
            , "ling"
            , "phil"
            , "soc_pla" ]

instance Interpretation Adjectives SynSem where
  combineR = Convenience.combineR
  combineL = Convenience.combineL
  
  lexica = [lex]
    where lex = \case
            "soccer player" -> [ SynSem {
                                   syn = noun,
                                   sem = ty tauAdj (purePP (lam x (lam i (sCon "soc_pla" @@ i @@ x))))
                                   } ]
            "linguist"      -> [ SynSem {
                                   syn = noun,
                                   sem = ty tauAdj (purePP (lam x (lam i (ling i @@ x))))
                                   } ]
            "philosopher"   -> [ SynSem {
                                   syn = noun,
                                   sem = ty tauAdj (purePP (lam x (lam i (phil i @@ x))))
                                   } ]
            "full"          -> [ SynSem {
                                   syn = ap \\ deg,
                                   sem = ty tauAdj (purePP (lam d (lam x (lam i (sCon "(≥)" @@ (sCon "height" @@ i @@ x) @@ d)))))
                                   }
                               , SynSem {
                                   syn = ap,
                                   sem = ty tauAdj (lam s (purePP (lam x (lam i (sCon "(≥)" @@ (sCon "height" @@ i @@ x) @@ (sCon "d_tall" @@ s)))) @@ s))
                                   } ]
            "tall"          -> [ SynSem {
                                   syn = ap \\ deg,
                                   sem = ty tauAdj (purePP (lam d (lam x (lam i (sCon "(≥)" @@ (sCon "height" @@ i @@ x) @@ d)))))
                                   }
                               , SynSem {
                                   syn = ap,
                                   sem = ty tauAdj (lam s (purePP (lam x (lam i (sCon "(≥)" @@ (sCon "height" @@ i @@ x) @@ (sCon "d_tall" @@ i)))) @@ s))
                                        } ]
            "jo"            -> [ SynSem {
                                   syn = np,
                                   sem = ty tauAdj (purePP (sCon "j"))
                                   }
                               , SynSem {
                                   syn = stnc // (stnc \\ np),
                                   sem = ty tauAdj (purePP (lam x (x @@ sCon "j")))
                                   } ]
            "bo"            -> [ SynSem {
                                   syn = np,
                                   sem = ty tauAdj (purePP (sCon "b"))
                                   }
                               , SynSem {
                                   syn = stnc // (stnc \\ np),
                                   sem = ty tauAdj (purePP (lam x (x @@ sCon "b")))
                                   } ]                  
            "every"         -> [ SynSem {
                                   syn = (stnc \\ np) \\ (stnc \\ np // np) // noun,
                                   sem = ty tauAdj (purePP (lam c (lam k (lam y (lam i (sCon "∀" @@ (lam x (sCon "(⇒)" @@ (c @@ x @@ i) @@ (k @@ x @@ y @@ i)))))))))
                                   }
                               , SynSem {
                                   syn = stnc // (stnc \\ np) // noun,
                                   sem = ty tauAdj (purePP (lam c (lam k (lam i (sCon "∀" @@ (lam x (sCon "(⇒)" @@ (c @@ x @@ i) @@ (k @@ x @@ i))))))))
                                   }
                               , SynSem {
                                   syn = stnc \\ (stnc // np) // noun,
                                   sem = ty tauAdj (purePP (lam c (lam k (lam i (sCon "∀" @@ (lam x (sCon "(⇒)" @@ (c @@ x @@ i) @@ (k @@ x @@ i))))))))
                                   } ]
            "a"             -> [ SynSem {
                                   syn = (stnc \\ np) \\ (stnc \\ np // np) // noun,
                                   sem = ty tauAdj (purePP (lam c (lam k (lam y (lam i (sCon "∃" @@ (lam x (sCon "(∧)" @@ (c @@ x @@ i) @@ (k @@ x @@ y @@ i)))))))))
                                   }
                               , SynSem {
                                   syn = stnc // (stnc \\ np) // noun,
                                   sem = ty tauAdj (purePP (lam c (lam k (lam i (sCon "∃" @@ (lam x (sCon "(∧)" @@ (c @@ x @@ i) @@ (k @@ x @@ i))))))))
                                   }
                               , SynSem {
                                   syn = stnc \\ (stnc // np) // noun,
                                   sem = ty tauAdj (purePP (lam c (lam k (lam i (sCon "∃" @@ (lam x (sCon "(∧)" @@ (c @@ x @@ i) @@ (k @@ x @@ i))))))))
                                   }
                               , SynSem {
                                   syn = np // noun,
                                   sem = ty tauAdj (purePP (lam x x))
                                   } ]
            "likely"      -> [ SynSem {
                                 syn = stnc \\ deg // stnc,
                                 sem = ty tauAdj (
                                     lam s (purePP (lam p (lam d (lam i (
                                                                     sCon "(≥)" @@ (
                                                                         Pr (let' j (CG s) (Return (p @@ (overwrite (context @Adjectives) i j))))
                                                                         ) @@ d
                                                                     )))) @@ s)
                                     )
                                 } ]
            "how"         -> [ SynSem {
                                 syn =  qDeg // (stnc // ap) // (ap \\ deg),
                                 sem = ty tauAdj (purePP (lam x (lam y (lam z (y @@ (x @@ z))))))
                                 }
                             , SynSem {
                                 syn = qDeg // (stnc \\ deg),
                                 sem = ty tauAdj (purePP (lam x x))
                                 } ]

            "is"            -> [ SynSem {
                                   syn = stnc \\ np // ap,
                                   sem = ty tauAdj (purePP (lam x x))
                                   }
                               , SynSem {
                                   syn = stnc \\ np // np,
                                   sem = ty tauAdj (purePP (lam x x))
                                   } ]
            "and"           -> [ SynSem {
                                   syn = stnc // (stnc \\ np) \\ (stnc // (stnc \\ np)) // (stnc // (stnc \\ np)),
                                   sem = ty tauAdj (purePP (lam m (lam n (lam k (lam i (sCon "(∧)" @@ (n @@ k @@ i) @@ (m @@ k @@ i)))))))
                                   }
                               , SynSem {
                                   syn = stnc \\ (stnc // np) \\ (stnc \\ (stnc // np)) // (stnc \\ (stnc // np)),
                                   sem = ty tauAdj (purePP (lam m (lam n (lam k (lam i (sCon "(∧)" @@ (n @@ k @@ i) @@ (m @@ k @@ i)))))))
                                   }
                               , SynSem {
                                   syn = (stnc \\ np) \\ (stnc \\ np // np) \\ ((stnc \\ np) \\ (stnc \\ np // np)) // ((stnc \\ np) \\ (stnc \\ np // np)),
                                   sem = ty tauAdj (purePP (lam m (lam n (lam k (lam x (lam i (sCon "(∧)" @@ (n @@ k @@ x @@ i) @@ (m @@ k @@ x @@ i))))))))
                                   }
                               , SynSem {
                                   syn = stnc \\ stnc // stnc,
                                   sem = ty tauAdj (purePP (lam m (lam n (lam i (sCon "(∧)" @@ (n @@ i) @@ (m @@ i))))))
                                   }
                               , SynSem {
                                   syn = stnc \\ np \\ (stnc \\ np) // (stnc \\ np),
                                   sem = ty tauAdj (purePP (lam m (lam n (lam x (lam i (sCon "(∧)" @@ (n @@ x @@ i) @@ (m @@ x @@ i)))))))
                                   }
                               , SynSem {
                                   syn = stnc \\ np // np \\ (stnc \\ np // np) // (stnc \\ np // np),
                                   sem = ty tauAdj (purePP (lam m (lam n (lam x (lam y (lam i (sCon "(∧)" @@ (n @@ x @@ y @@ i) @@ (m @@ x @@ y @@ i))))))))
                                   } ]
            "that"        -> [ SynSem {
                                 syn = stnc // stnc,
                                 sem = ty tauAdj (purePP (lam x x))
                                 } ]


--------------------------------------------------------------------------------
-- * Priors and response functions

-- | Prior to be used for the scale-norming example.
scaleNormingPrior :: Term
scaleNormingPrior = Return (upd_CG cg' ϵ)
  where cg' = let' b (Bern (dCon 0.5)) (let' x (normal 0 1) (let' y (normal 0 1) j'))
        j'  = Return (UpdHeight (lam z (ITE (SocPla i' @@ z) x y)) i')
        i'  = UpdSocPla (lam x b) _0

-- | Prior to be used for the likelihood example.
likelihoodPrior :: Term
likelihoodPrior = Return (upd_CG cg' ϵ)
  where cg' = let' x (normal 0 1) (let' y (normal 0 1) (let' w (LogitNormal 0 1) (let' b (Bern w) (Return (Upd "d_tall" x (Upd "height" (lam z y) (Upd "soc_pla" (lam z b) _0)))))))

-- | Response function to be used for adjectives examples.
adjectivesRespond :: Term -> Term -> Term
adjectivesRespond = respond (lam x (Normal x (Var "sigma")))
