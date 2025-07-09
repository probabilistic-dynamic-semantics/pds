{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-|
Module      : Analysis.Factivity.Factivity
Description : Factivity lexicon.
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com
-}

module Analysis.Factivity.Factivity where

import Analysis.Factivity.Signature
import Framework.Grammar.CCG
import Framework.Grammar.Lexica.SynSem
import Framework.Grammar.Lexica.SynSem.Convenience as Convenience
import Framework.Lambda

--------------------------------------------------------------------------------
-- * Lexica for factivity

instance Interpretation Factivity SynSem where
  combineR = Convenience.combineR
  combineL = Convenience.combineL
  
  lexica = [lex]
    where lex = \case
            "knows"       -> [ SynSem {
                                 syn = Base "s" \\ Base "np" // Base "s",
                                 sem = ty tauFact (lam s (purePP (lam p (lam x (lam i (ITE (TauKnow s) (And (epi i @@ x @@ p) (p @@ i)) (epi i @@ x @@ p))))) @@ s))
                                 } ]
            "linguist"    -> [ SynSem {
                                 syn = Base "n",
                                 sem = ty tauFact (purePP (lam x (lam i (ling i @@ x))))
                                 } ]
            "philosopher" -> [ SynSem {
                                 syn = Base "n",
                                 sem = ty tauFact (purePP (lam x (lam i (phil i @@ x))))
                                 } ]
            "jo"          -> [ SynSem {
                                 syn = Base "np",
                                 sem = ty tauFact (purePP (sCon "j"))
                                 }
                             , SynSem {
                                 syn = Base "s" // (Base "s" \\ Base "np"),
                                 sem = ty tauFact (purePP (lam x (x @@ sCon "j")))
                                 } ]
            "bo"          -> [ SynSem {
                                 syn = Base "np",
                                 sem = ty tauFact (purePP (sCon "b"))
                                 }
                             , SynSem {
                                 syn = Base "s" // (Base "s" \\ Base "np"),
                                 sem = ty tauFact (purePP (lam x (x @@ sCon "b")))
                                 } ]
            "every"       -> [ SynSem {
                                 syn = (Base "s" \\ Base "np") \\ (Base "s" \\ Base "np" // Base "np") // Base "n",
                                 sem = ty tauFact (purePP (lam c (lam k (lam y (lam i (sCon "∀" @@ (lam x (sCon "(⇒)" @@ (c @@ x @@ i) @@ (k @@ x @@ y @@ i)))))))))
                                 }
                             , SynSem {
                                 syn = Base "s" // (Base "s" \\ Base "np") // Base "n",
                                 sem = ty tauFact (purePP (lam c (lam k (lam i (sCon "∀" @@ (lam x (sCon "(⇒)" @@ (c @@ x @@ i) @@ (k @@ x @@ i))))))))
                                 }
                             , SynSem {
                                 syn = Base "s" \\ (Base "s" // Base "np") // Base "n",
                                 sem = ty tauFact (purePP (lam c (lam k (lam i (sCon "∀" @@ (lam x (sCon "(⇒)" @@ (c @@ x @@ i) @@ (k @@ x @@ i))))))))
                                 } ]
            "a"           -> [ SynSem {
                                 syn = (Base "s" \\ Base "np") \\ (Base "s" \\ Base "np" // Base "np") // Base "n",
                                 sem = ty tauFact (purePP (lam c (lam k (lam y (lam i (sCon "∃" @@ (lam x (sCon "(∧)" @@ (c @@ x @@ i) @@ (k @@ x @@ y @@ i)))))))))
                                 }
                             , SynSem {
                                 syn = Base "s" // (Base "s" \\ Base "np") // Base "n",
                                 sem = ty tauFact (purePP (lam c (lam k (lam i (sCon "∃" @@ (lam x (sCon "(∧)" @@ (c @@ x @@ i) @@ (k @@ x @@ i))))))))
                                 }
                             , SynSem {
                                 syn = Base "s" \\ (Base "s" // Base "np") // Base "n",
                                 sem = ty tauFact (purePP (lam c (lam k (lam i (sCon "∃" @@ (lam x (sCon "(∧)" @@ (c @@ x @@ i) @@ (k @@ x @@ i))))))))
                                 }
                             , SynSem {
                                 syn = Base "np" // Base "n",
                                 sem = ty tauFact (purePP (lam x x))
                                 } ]
            "likely"      -> [ SynSem {
                                 syn = Base "s" \\ Base "deg" // Base "s",
                                 sem = ty tauFact (
                                     lam s (purePP (lam p (lam d (lam i (
                                                                     sCon "(≥)" @@ (
                                                                         Pr (let' j (CG s) (Return (p @@ (overwrite contextParams i j))))
                                                                         ) @@ d
                                                                     )))) @@ s)
                                     )
                                 } ]
            "how"         -> [ SynSem {
                                 syn =  Base "qDeg" // (Base "s" // Base "ap") // (Base "ap" \\ Base "deg"),
                                 sem = ty tauFact (purePP (lam x (lam y (lam z (y @@ (x @@ z))))))
                                 }
                             , SynSem {
                                 syn = Base "qDeg" // (Base "s" \\ Base "deg"),
                                 sem = ty tauFact (purePP (lam x x))
                                 } ]
            "is"          -> [ SynSem {
                                 syn = Base "s" \\ Base "np" // Base "ap",
                                 sem = ty tauFact (purePP (lam x x))
                                 }
                             , SynSem {
                                 syn = Base "s" \\ Base "np" // Base "np",
                                 sem = ty tauFact (purePP (lam x x))
                                 } ]
            "and"         -> [ SynSem {
                                 syn = Base "s" // (Base "s" \\ Base "np") \\ (Base "s" // (Base "s" \\ Base "np")) // (Base "s" // (Base "s" \\ Base "np")),
                                 sem = ty tauFact (purePP (lam m (lam n (lam k (lam i (sCon "(∧)" @@ (n @@ k @@ i) @@ (m @@ k @@ i)))))))
                                 }
                             , SynSem {
                                 syn = Base "s" \\ (Base "s" // Base "np") \\ (Base "s" \\ (Base "s" // Base "np")) // (Base "s" \\ (Base "s" // Base "np")),
                                 sem = ty tauFact (purePP (lam m (lam n (lam k (lam i (sCon "(∧)" @@ (n @@ k @@ i) @@ (m @@ k @@ i)))))))
                                 }
                             , SynSem {
                                 syn = (Base "s" \\ Base "np") \\ (Base "s" \\ Base "np" // Base "np") \\ ((Base "s" \\ Base "np") \\ (Base "s" \\ Base "np" // Base "np")) // ((Base "s" \\ Base "np") \\ (Base "s" \\ Base "np" // Base "np")),
                                 sem = ty tauFact (purePP (lam m (lam n (lam k (lam x (lam i (sCon "(∧)" @@ (n @@ k @@ x @@ i) @@ (m @@ k @@ x @@ i))))))))
                                 }
                             , SynSem {
                                 syn = Base "s" \\ Base "s" // Base "s",
                                 sem = ty tauFact (purePP (lam m (lam n (lam i (sCon "(∧)" @@ (n @@ i) @@ (m @@ i))))))
                                 }
                             , SynSem {
                                 syn = Base "s" \\ Base "np" \\ (Base "s" \\ Base "np") // (Base "s" \\ Base "np"),
                                 sem = ty tauFact (purePP (lam m (lam n (lam x (lam i (sCon "(∧)" @@ (n @@ x @@ i) @@ (m @@ x @@ i)))))))
                                 }
                             , SynSem {
                                 syn = Base "s" \\ Base "np" // Base "np" \\ (Base "s" \\ Base "np" // Base "np") // (Base "s" \\ Base "np" // Base "np"),
                                 sem = ty tauFact (purePP (lam m (lam n (lam x (lam y (lam i (sCon "(∧)" @@ (n @@ x @@ y @@ i) @@ (m @@ x @@ y @@ i))))))))
                                 }
                             ]
            "that"        -> [ SynSem {
                                 syn = Base "s" // Base "s",
                                 sem = ty tauFact (purePP (lam x x))
                                 } ]

--------------------------------------------------------------------------------
-- * Priors and response functions


-- | Prior to be used for the factivity example.
factivityPrior :: Term
factivityPrior = let' x (LogitNormal 0 1) (let' y (LogitNormal 0 1) (let' z (LogitNormal 0 1) (let' b (Bern x) (Return (UpdCG (let' c (Bern y) (let' d (Bern z) (Return (UpdLing (lam x c) (UpdEpi (lam x (lam p d)) _0))))) (UpdTauKnow b ϵ))))))

-- | Respones function to be used for the factivity example.
factivityRespond :: Term -> Term -> Term
factivityRespond = respond (lam x (Truncate (Normal x (Var "sigma")) 0 1))
