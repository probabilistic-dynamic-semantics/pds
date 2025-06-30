{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-|
Module      : Analysis.Adjectives.Adjectives
Description : Adjectives lexicon.
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com
-}

module Analysis.Adjectives.Adjectives where

import Framework.Grammar.CCG
import Framework.Grammar.Lexica.SynSem
import Framework.Grammar.Lexica.SynSem.Convenience as Convenience
import Framework.Lambda
import Theory.Signature

--------------------------------------------------------------------------------
-- * Lexica for adjectives

instance Interpretation Adjectives SynSem where
  combineR = Convenience.combineR
  combineL = Convenience.combineL
  
  lexica = [lex]
    where lex = \case
            "soccer player" -> [ SynSem {
                                   syn = Base "n",
                                   sem = ty tau (purePP (lam x (lam i (sCon "soc_pla" @@ i @@ x))))
                                   } ]
            "linguist"      -> [ SynSem {
                                   syn = Base "n",
                                   sem = ty tau (purePP (lam x (lam i (ling i @@ x))))
                                   } ]
            "philosopher"   -> [ SynSem {
                                   syn = Base "n",
                                   sem = ty tau (purePP (lam x (lam i (phil i @@ x))))
                                   } ]
            "full"          -> [ SynSem {
                                   syn = Base "ap" \\ Base "deg",
                                   sem = ty tau (purePP (lam d (lam x (lam i (sCon "(≥)" @@ (sCon "height" @@ i @@ x) @@ d)))))
                                   }
                               , SynSem {
                                   syn = Base "ap",
                                   sem = ty tau (lam s (purePP (lam x (lam i (sCon "(≥)" @@ (sCon "height" @@ i @@ x) @@ (sCon "d_tall" @@ s)))) @@ s))
                                   } ]
            "tall"          -> [ SynSem {
                                   syn = Base "ap" \\ Base "deg",
                                   sem = ty tau (purePP (lam d (lam x (lam i (sCon "(≥)" @@ (sCon "height" @@ i @@ x) @@ d)))))
                                   }
                               , SynSem {
                                   syn = Base "ap",
                                   sem = ty tau (lam s (purePP (lam x (lam i (sCon "(≥)" @@ (sCon "height" @@ i @@ x) @@ (sCon "d_tall" @@ s)))) @@ s))
                                        } ]
            "jo"            -> [ SynSem {
                                   syn = Base "np",
                                   sem = ty tau (purePP (sCon "j"))
                                   }
                               , SynSem {
                                   syn = Base "s" // (Base "s" \\ Base "np"),
                                   sem = ty tau (purePP (lam x (x @@ sCon "j")))
                                   } ]
            "bo"            -> [ SynSem {
                                   syn = Base "np",
                                   sem = ty tau (purePP (sCon "b"))
                                   }
                               , SynSem {
                                   syn = Base "s" // (Base "s" \\ Base "np"),
                                   sem = ty tau (purePP (lam x (x @@ sCon "b")))
                                   } ]                  
            "every"         -> [ SynSem {
                                   syn = (Base "s" \\ Base "np") \\ (Base "s" \\ Base "np" // Base "np") // Base "n",
                                   sem = ty tau (purePP (lam c (lam k (lam y (lam i (sCon "∀" @@ (lam x (sCon "(⇒)" @@ (c @@ x @@ i) @@ (k @@ x @@ y @@ i)))))))))
                                   }
                               , SynSem {
                                   syn = Base "s" // (Base "s" \\ Base "np") // Base "n",
                                   sem = ty tau (purePP (lam c (lam k (lam i (sCon "∀" @@ (lam x (sCon "(⇒)" @@ (c @@ x @@ i) @@ (k @@ x @@ i))))))))
                                   }
                               , SynSem {
                                   syn = Base "s" \\ (Base "s" // Base "np") // Base "n",
                                   sem = ty tau (purePP (lam c (lam k (lam i (sCon "∀" @@ (lam x (sCon "(⇒)" @@ (c @@ x @@ i) @@ (k @@ x @@ i))))))))
                                   } ]
            "a"             -> [ SynSem {
                                   syn = (Base "s" \\ Base "np") \\ (Base "s" \\ Base "np" // Base "np") // Base "n",
                                   sem = ty tau (purePP (lam c (lam k (lam y (lam i (sCon "∃" @@ (lam x (sCon "(∧)" @@ (c @@ x @@ i) @@ (k @@ x @@ y @@ i)))))))))
                                   }
                               , SynSem {
                                   syn = Base "s" // (Base "s" \\ Base "np") // Base "n",
                                   sem = ty tau (purePP (lam c (lam k (lam i (sCon "∃" @@ (lam x (sCon "(∧)" @@ (c @@ x @@ i) @@ (k @@ x @@ i))))))))
                                   }
                               , SynSem {
                                   syn = Base "s" \\ (Base "s" // Base "np") // Base "n",
                                   sem = ty tau (purePP (lam c (lam k (lam i (sCon "∃" @@ (lam x (sCon "(∧)" @@ (c @@ x @@ i) @@ (k @@ x @@ i))))))))
                                   }
                               , SynSem {
                                   syn = Base "np" // Base "n",
                                   sem = ty tau (purePP (lam x x))
                                   } ]
            "likely"      -> [ SynSem {
                                 syn = Base "s" \\ Base "deg" // Base "s",
                                 sem = ty tau (lam s (purePP (lam p (lam d (lam _' (sCon "(≥)" @@ (Pr (let' i (CG s) (Return (p @@ i)))) @@ d)))) @@ s))
                                 } ]
            "how"         -> [ SynSem {
                                 syn =  Base "qDeg" // (Base "s" // Base "ap") // (Base "ap" \\ Base "deg"),
                                 sem = ty tau (purePP (lam x (lam y (lam z (y @@ (x @@ z))))))
                                 }
                             , SynSem {
                                 syn = Base "qDeg" // (Base "s" \\ Base "deg"),
                                 sem = ty tau (purePP (lam x x))
                                 } ]

            "is"            -> [ SynSem {
                                   syn = Base "s" \\ Base "np" // Base "ap",
                                   sem = ty tau (purePP (lam x x))
                                   }
                               , SynSem {
                                   syn = Base "s" \\ Base "np" // Base "np",
                                   sem = ty tau (purePP (lam x x))
                                   } ]
            "and"           -> [ SynSem {
                                   syn = Base "s" // (Base "s" \\ Base "np") \\ (Base "s" // (Base "s" \\ Base "np")) // (Base "s" // (Base "s" \\ Base "np")),
                                   sem = ty tau (purePP (lam m (lam n (lam k (lam i (sCon "(∧)" @@ (n @@ k @@ i) @@ (m @@ k @@ i)))))))
                                   }
                               , SynSem {
                                   syn = Base "s" \\ (Base "s" // Base "np") \\ (Base "s" \\ (Base "s" // Base "np")) // (Base "s" \\ (Base "s" // Base "np")),
                                   sem = ty tau (purePP (lam m (lam n (lam k (lam i (sCon "(∧)" @@ (n @@ k @@ i) @@ (m @@ k @@ i)))))))
                                   }
                               , SynSem {
                                   syn = (Base "s" \\ Base "np") \\ (Base "s" \\ Base "np" // Base "np") \\ ((Base "s" \\ Base "np") \\ (Base "s" \\ Base "np" // Base "np")) // ((Base "s" \\ Base "np") \\ (Base "s" \\ Base "np" // Base "np")),
                                   sem = ty tau (purePP (lam m (lam n (lam k (lam x (lam i (sCon "(∧)" @@ (n @@ k @@ x @@ i) @@ (m @@ k @@ x @@ i))))))))
                                   }
                               , SynSem {
                                   syn = Base "s" \\ Base "s" // Base "s",
                                   sem = ty tau (purePP (lam m (lam n (lam i (sCon "(∧)" @@ (n @@ i) @@ (m @@ i))))))
                                   }
                               , SynSem {
                                   syn = Base "s" \\ Base "np" \\ (Base "s" \\ Base "np") // (Base "s" \\ Base "np"),
                                   sem = ty tau (purePP (lam m (lam n (lam x (lam i (sCon "(∧)" @@ (n @@ x @@ i) @@ (m @@ x @@ i)))))))
                                   }
                               , SynSem {
                                   syn = Base "s" \\ Base "np" // Base "np" \\ (Base "s" \\ Base "np" // Base "np") // (Base "s" \\ Base "np" // Base "np"),
                                   sem = ty tau (purePP (lam m (lam n (lam x (lam y (lam i (sCon "(∧)" @@ (n @@ x @@ y @@ i) @@ (m @@ x @@ y @@ i))))))))
                                   } ]
            "that"        -> [ SynSem {
                                 syn = Base "s" // Base "s",
                                 sem = ty tau (purePP (lam x x))
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
likelihoodPrior = let' x (normal 0 1) (Return (UpdDTall x (upd_CG cg' ϵ)))
  where cg' = let' y (normal 0 1) (let' w (LogitNormal 0 1) (let' b (Bern w) (Return (UpdHeight (lam z y) (UpdSocPla (lam z b) _0)))))

-- | Prior to be used for the likelihood example for relative adjectives (/tall/).
likelihoodPriorRelative :: Term
likelihoodPriorRelative = let' x (normal 0 1) (let' y (normal 0 1) (Return (UpdDTall x (upd_CG cg' ϵ))))
  where cg' = let' y (normal 0 1) (let' w (LogitNormal 0 1) (let' b (Bern w) (Return (UpdHeight (lam z y) (UpdSocPla (lam z b) _0)))))

-- | Respones function to be used for adjective examples.
adjectivesRespond :: Term -> Term -> Term
adjectivesRespond = respond (lam x (Normal x (Var "sigma")))
