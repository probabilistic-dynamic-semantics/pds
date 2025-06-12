{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-|
Module      : Grammar.Lexica.SynSem
Description : Adjectives lexicon.
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com
-}

module Grammar.Lexica.SynSem.Adjectives where

import Grammar.CCG
import Grammar.Lexica.SynSem
import Grammar.Lexica.SynSem.Convenience as Convenience
import Lambda

--------------------------------------------------------------------------------
-- * Lexica for adjectives

instance Interpretation Adjectives SynSem where
  combineR = Convenience.combineR
  combineL = Convenience.combineL
  
  lexica = [lex]
    where lex = \case
            "soccer player" -> [ SynSem {
                                   syn = N,
                                   sem = ty tau (purePP (lam x (lam i (sCon "soc_pla" @@ i @@ x))))
                                   } ]
            "linguist"      -> [ SynSem {
                                   syn = N,
                                   sem = ty tau (purePP (lam x (lam i (ling i @@ x))))
                                   } ]
            "philosopher"   -> [ SynSem {
                                   syn = N,
                                   sem = ty tau (purePP (lam x (lam i (phil i @@ x))))
                                   } ]
            "tall"          -> [ SynSem {
                                   syn = AP :\: Deg,
                                   sem = ty tau (purePP (lam d (lam x (lam i (sCon "(≥)" @@ (sCon "tall" @@ i @@ x) @@ d)))))
                                   } ]
            "jo"            -> [ SynSem {
                                   syn = NP,
                                   sem = ty tau (purePP (sCon "j"))
                                   }
                               , SynSem {
                                   syn = S :/: (S :\: NP),
                                   sem = ty tau (purePP (lam x (x @@ sCon "j")))
                                   } ]
            "bo"            -> [ SynSem {
                                   syn = NP,
                                   sem = ty tau (purePP (sCon "b"))
                                   }
                               , SynSem {
                                   syn = S :/: (S :\: NP),
                                   sem = ty tau (purePP (lam x (x @@ sCon "b")))
                                   } ]                  
            "every"         -> [ SynSem {
                                   syn = (S :\: NP) :\: (S :\: NP :/: NP) :/: N,
                                   sem = ty tau (purePP (lam c (lam k (lam y (lam i (sCon "∀" @@ (lam x (sCon "(⇒)" @@ (c @@ x @@ i) @@ (k @@ x @@ y @@ i)))))))))
                                   }
                               , SynSem {
                                   syn = S :/: (S :\: NP) :/: N,
                                   sem = ty tau (purePP (lam c (lam k (lam i (sCon "∀" @@ (lam x (sCon "(⇒)" @@ (c @@ x @@ i) @@ (k @@ x @@ i))))))))
                                   }
                               , SynSem {
                                   syn = S :\: (S :/: NP) :/: N,
                                   sem = ty tau (purePP (lam c (lam k (lam i (sCon "∀" @@ (lam x (sCon "(⇒)" @@ (c @@ x @@ i) @@ (k @@ x @@ i))))))))
                                   } ]
            "a"             -> [ SynSem {
                                   syn = (S :\: NP) :\: (S :\: NP :/: NP) :/: N,
                                   sem = ty tau (purePP (lam c (lam k (lam y (lam i (sCon "∃" @@ (lam x (sCon "(∧)" @@ (c @@ x @@ i) @@ (k @@ x @@ y @@ i)))))))))
                                   }
                               , SynSem {
                                   syn = S :/: (S :\: NP) :/: N,
                                   sem = ty tau (purePP (lam c (lam k (lam i (sCon "∃" @@ (lam x (sCon "(∧)" @@ (c @@ x @@ i) @@ (k @@ x @@ i))))))))
                                   }
                               , SynSem {
                                   syn = S :\: (S :/: NP) :/: N,
                                   sem = ty tau (purePP (lam c (lam k (lam i (sCon "∃" @@ (lam x (sCon "(∧)" @@ (c @@ x @@ i) @@ (k @@ x @@ i))))))))
                                   }
                               , SynSem {
                                   syn = NP :/: N,
                                   sem = ty tau (purePP (lam x x))
                                   } ]
            "likely"        -> [ SynSem {
                                   syn = Qdeg :/: S,
                                   sem = ty tau (lam s (purePP (lam p (lam d (lam _' (sCon "(≥)" @@ (Pr (let' i (CG s) (Return (p @@ i)))) @@ d)))) @@ s))
                                   } ]
            "how"           -> [ SynSem {
                                   syn =  Qdeg :/: (S :/: AP) :/: (AP :\: Deg),
                                   sem = ty tau (purePP (lam x (lam y (lam z (y @@ (x @@ z))))))
                                   } ]
            "is"            -> [ SynSem {
                                   syn = S :\: NP :/: AP,
                                   sem = ty tau (purePP (lam x x))
                                   }
                               , SynSem {
                                   syn = S :\: NP :/: NP,
                                   sem = ty tau (purePP (lam x x))
                                   } ]
            "and"           -> [ SynSem {
                                   syn = S :/: (S :\: NP) :\: (S :/: (S :\: NP)) :/: (S :/: (S :\: NP)),
                                   sem = ty tau (purePP (lam m (lam n (lam k (lam i (sCon "(∧)" @@ (n @@ k @@ i) @@ (m @@ k @@ i)))))))
                                   }
                               , SynSem {
                                   syn = S :\: (S :/: NP) :\: (S :\: (S :/: NP)) :/: (S :\: (S :/: NP)),
                                   sem = ty tau (purePP (lam m (lam n (lam k (lam i (sCon "(∧)" @@ (n @@ k @@ i) @@ (m @@ k @@ i)))))))
                                   }
                               , SynSem {
                                   syn = (S :\: NP) :\: (S :\: NP :/: NP) :\: ((S :\: NP) :\: (S :\: NP :/: NP)) :/: ((S :\: NP) :\: (S :\: NP :/: NP)),
                                   sem = ty tau (purePP (lam m (lam n (lam k (lam x (lam i (sCon "(∧)" @@ (n @@ k @@ x @@ i) @@ (m @@ k @@ x @@ i))))))))
                                   }
                               , SynSem {
                                   syn = S :\: S :/: S,
                                   sem = ty tau (purePP (lam m (lam n (lam i (sCon "(∧)" @@ (n @@ i) @@ (m @@ i))))))
                                   }
                               , SynSem {
                                   syn = S :\: NP :\: (S :\: NP) :/: (S :\: NP),
                                   sem = ty tau (purePP (lam m (lam n (lam x (lam i (sCon "(∧)" @@ (n @@ x @@ i) @@ (m @@ x @@ i)))))))
                                   }
                               , SynSem {
                                   syn = S :\: NP :/: NP :\: (S :\: NP :/: NP) :/: (S :\: NP :/: NP),
                                   sem = ty tau (purePP (lam m (lam n (lam x (lam y (lam i (sCon "(∧)" @@ (n @@ x @@ y @@ i) @@ (m @@ x @@ y @@ i))))))))
                                   } ]

--------------------------------------------------------------------------------
-- * Priors and response functions

-- | Prior to be used for the scale-norming example.
scaleNormingPrior :: Term
scaleNormingPrior = Return (upd_CG cg' ϵ)
  where cg' = let' b (Bern (dCon 0.5)) (let' x (normal 0 1) (let' y (normal 0 1) j'))
        j'  = Return (UpdTall (lam z (ITE (SocPla i' @@ z) x y)) i')
        i'  = UpdSocPla (lam x b) _0


-- | Respones function to be used for the scale-norming example.
scaleNormingRespond :: Term -> Term -> Term
scaleNormingRespond = respond (lam x (Normal x (Var "sigma")))
