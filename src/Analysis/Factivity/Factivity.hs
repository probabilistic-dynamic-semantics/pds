{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}

{-|
Module      : Analysis.Factivity.Factivity
Description : Factivity lexicon.
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com
-}

module Analysis.Factivity.Factivity where

import Analysis.Factivity.Signature
import Framework.Grammar.Convenience
import Framework.Grammar.CCG
import Framework.Grammar.Lexica.SynSem
import Framework.Grammar.Lexica.SynSem.Convenience as Convenience
import Framework.Lambda

--------------------------------------------------------------------------------
-- * Lexica for factivity

instance Indices Factivity where
  context = []
  world   = [ "ling"
            , "phil" ]

instance Interpretation Factivity SynSem where
  combineR = Convenience.combineR
  combineL = Convenience.combineL
  
  lexica = [lex]
    where lex = \case
            "knows"       -> [ SynSem {
                                 syn = stnc \\ np // stnc,
                                 sem = ty tauFact (lam s (purePP (lam p (lam x (lam i (ITE (TauKnow s) (And (epi i @@ x @@ p) (p @@ i)) (epi i @@ x @@ p))))) @@ s))
                                 } ]
            "linguist"    -> [ SynSem {
                                 syn = noun,
                                 sem = ty tauFact (purePP (lam x (lam i (ling i @@ x))))
                                 } ]
            "philosopher" -> [ SynSem {
                                 syn = noun,
                                 sem = ty tauFact (purePP (lam x (lam i (phil i @@ x))))
                                 } ]
            "jo"          -> [ SynSem {
                                 syn = np,
                                 sem = ty tauFact (purePP (sCon "j"))
                                 }
                             , SynSem {
                                 syn = stnc // (stnc \\ np),
                                 sem = ty tauFact (purePP (lam x (x @@ sCon "j")))
                                 } ]
            "bo"          -> [ SynSem {
                                 syn = np,
                                 sem = ty tauFact (purePP (sCon "b"))
                                 }
                             , SynSem {
                                 syn = stnc // (stnc \\ np),
                                 sem = ty tauFact (purePP (lam x (x @@ sCon "b")))
                                 } ]
            "every"       -> [ SynSem {
                                 syn = (stnc \\ np) \\ (stnc \\ np // np) // noun,
                                 sem = ty tauFact (purePP (lam c (lam k (lam y (lam i (sCon "∀" @@ (lam x (sCon "(⇒)" @@ (c @@ x @@ i) @@ (k @@ x @@ y @@ i)))))))))
                                 }
                             , SynSem {
                                 syn = stnc // (stnc \\ np) // noun,
                                 sem = ty tauFact (purePP (lam c (lam k (lam i (sCon "∀" @@ (lam x (sCon "(⇒)" @@ (c @@ x @@ i) @@ (k @@ x @@ i))))))))
                                 }
                             , SynSem {
                                 syn = stnc \\ (stnc // np) // noun,
                                 sem = ty tauFact (purePP (lam c (lam k (lam i (sCon "∀" @@ (lam x (sCon "(⇒)" @@ (c @@ x @@ i) @@ (k @@ x @@ i))))))))
                                 } ]
            "a"           -> [ SynSem {
                                 syn = (stnc \\ np) \\ (stnc \\ np // np) // noun,
                                 sem = ty tauFact (purePP (lam c (lam k (lam y (lam i (sCon "∃" @@ (lam x (sCon "(∧)" @@ (c @@ x @@ i) @@ (k @@ x @@ y @@ i)))))))))
                                 }
                             , SynSem {
                                 syn = stnc // (stnc \\ np) // noun,
                                 sem = ty tauFact (purePP (lam c (lam k (lam i (sCon "∃" @@ (lam x (sCon "(∧)" @@ (c @@ x @@ i) @@ (k @@ x @@ i))))))))
                                 }
                             , SynSem {
                                 syn = stnc \\ (stnc // np) // noun,
                                 sem = ty tauFact (purePP (lam c (lam k (lam i (sCon "∃" @@ (lam x (sCon "(∧)" @@ (c @@ x @@ i) @@ (k @@ x @@ i))))))))
                                 }
                             , SynSem {
                                 syn = np // noun,
                                 sem = ty tauFact (purePP (lam x x))
                                 } ]
            "likely"      -> [ SynSem {
                                 syn = stnc \\ deg // stnc,
                                 sem = ty tauFact (
                                     lam s (purePP (lam p (lam d (lam i (
                                                                     sCon "(≥)" @@ (
                                                                         Pr (let' j (CG s) (Return (p @@ (overwrite (context @Factivity) i j))))
                                                                         ) @@ d
                                                                     )))) @@ s)
                                     )
                                 } ]
            "how"         -> [ SynSem {
                                 syn =  qDeg // (stnc // ap) // (ap \\ deg),
                                 sem = ty tauFact (purePP (lam x (lam y (lam z (y @@ (x @@ z))))))
                                 }
                             , SynSem {
                                 syn = qDeg // (stnc \\ deg),
                                 sem = ty tauFact (purePP (lam x x))
                                 } ]
            "is"          -> [ SynSem {
                                 syn = stnc \\ np // ap,
                                 sem = ty tauFact (purePP (lam x x))
                                 }
                             , SynSem {
                                 syn = stnc \\ np // np,
                                 sem = ty tauFact (purePP (lam x x))
                                 } ]
            "and"         -> [ SynSem {
                                 syn = stnc // (stnc \\ np) \\ (stnc // (stnc \\ np)) // (stnc // (stnc \\ np)),
                                 sem = ty tauFact (purePP (lam m (lam n (lam k (lam i (sCon "(∧)" @@ (n @@ k @@ i) @@ (m @@ k @@ i)))))))
                                 }
                             , SynSem {
                                 syn = stnc \\ (stnc // np) \\ (stnc \\ (stnc // np)) // (stnc \\ (stnc // np)),
                                 sem = ty tauFact (purePP (lam m (lam n (lam k (lam i (sCon "(∧)" @@ (n @@ k @@ i) @@ (m @@ k @@ i)))))))
                                 }
                             , SynSem {
                                 syn = (stnc \\ np) \\ (stnc \\ np // np) \\ ((stnc \\ np) \\ (stnc \\ np // np)) // ((stnc \\ np) \\ (stnc \\ np // np)),
                                 sem = ty tauFact (purePP (lam m (lam n (lam k (lam x (lam i (sCon "(∧)" @@ (n @@ k @@ x @@ i) @@ (m @@ k @@ x @@ i))))))))
                                 }
                             , SynSem {
                                 syn = stnc \\ stnc // stnc,
                                 sem = ty tauFact (purePP (lam m (lam n (lam i (sCon "(∧)" @@ (n @@ i) @@ (m @@ i))))))
                                 }
                             , SynSem {
                                 syn = stnc \\ np \\ (stnc \\ np) // (stnc \\ np),
                                 sem = ty tauFact (purePP (lam m (lam n (lam x (lam i (sCon "(∧)" @@ (n @@ x @@ i) @@ (m @@ x @@ i)))))))
                                 }
                             , SynSem {
                                 syn = stnc \\ np // np \\ (stnc \\ np // np) // (stnc \\ np // np),
                                 sem = ty tauFact (purePP (lam m (lam n (lam x (lam y (lam i (sCon "(∧)" @@ (n @@ x @@ y @@ i) @@ (m @@ x @@ y @@ i))))))))
                                 }
                             ]
            "that"        -> [ SynSem {
                                 syn = stnc // stnc,
                                 sem = ty tauFact (purePP (lam x x))
                                 } ]

--------------------------------------------------------------------------------
-- * Priors and response functions


-- | Prior to be used for the factivity example.
factivityPrior :: Term
factivityPrior = let' x (LogitNormal 0 1) (let' y (LogitNormal 0 1) (let' z (LogitNormal 0 1) (let' b (Bern x) (Return (UpdCG (let' c (Bern y) (let' d (Bern z) (Return (UpdLing (lam x c) (UpdEpi (lam x (lam p d)) _0))))) (UpdTauKnow b ϵ))))))

-- | Response function to be used for the factivity example.
factivityRespond :: Term -> Term -> Term
factivityRespond = respond (lam x (Truncate (Normal x (Var "sigma")) 0 1))
