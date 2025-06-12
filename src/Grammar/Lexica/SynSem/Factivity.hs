{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-|
Module      : Grammar.Lexica.SynSem.Factivity
Description : Factivity lexicon.
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com
-}

module Grammar.Lexica.SynSem.Factivity where

import Grammar.CCG
import Grammar.Lexica.SynSem
import Grammar.Lexica.SynSem.Convenience as Convenience
import Lambda

--------------------------------------------------------------------------------
-- * Lexica for factivity

instance Interpretation Factivity SynSem where
  combineR = Convenience.combineR
  combineL = Convenience.combineL
  
  lexica = [lex]
    where lex = \case
            "knows"       -> [ SynSem {
                                 syn = S :\: NP :/: S,
                                 sem = ty tau (lam s (purePP (lam p (lam x (lam i (ITE (TauKnow s) (And (epi i @@ x @@ p) (p @@ i)) (epi i @@ x @@ p))))) @@ s))
                                 } ]
            "linguist"    -> [ SynSem {
                                 syn = N,
                                 sem = ty tau (purePP (lam x (lam i (ling i @@ x))))
                                 } ]
            "philosopher" -> [ SynSem {
                                 syn = N,
                                 sem = ty tau (purePP (lam x (lam i (phil i @@ x))))
                                 } ]
            "jo"          -> [ SynSem {
                                 syn = NP,
                                 sem = ty tau (purePP (sCon "j"))
                                 }
                             , SynSem {
                                 syn = S :/: (S :\: NP),
                                 sem = ty tau (purePP (lam x (x @@ sCon "j")))
                                 } ]
            "bo"          -> [ SynSem {
                                 syn = NP,
                                 sem = ty tau (purePP (sCon "b"))
                                 }
                             , SynSem {
                                 syn = S :/: (S :\: NP),
                                 sem = ty tau (purePP (lam x (x @@ sCon "b")))
                                 } ]
            "every"       -> [ SynSem {
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
            "a"           -> [ SynSem {
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
            "likely"      -> [ SynSem {
                                 syn = S :\: Deg :/: S,
                                 sem = ty tau (lam s (purePP (lam p (lam d (lam _' (sCon "(≥)" @@ (Pr (let' i (CG s) (Return (p @@ i)))) @@ d)))) @@ s))
                                 } ]
            "how"         -> [ SynSem {
                                 syn =  Qdeg :/: (S :/: AP) :/: (AP :\: Deg),
                                 sem = ty tau (purePP (lam x (lam y (lam z (y @@ (x @@ z))))))
                                 }
                             , SynSem {
                                 syn = Qdeg :/: (S :\: Deg),
                                 sem = ty tau (purePP (lam x x))
                                 } ]
            "is"          -> [ SynSem {
                                 syn = S :\: NP :/: AP,
                                 sem = ty tau (purePP (lam x x))
                                 }
                             , SynSem {
                                 syn = S :\: NP :/: NP,
                                 sem = ty tau (purePP (lam x x))
                                 } ]
            "and"         -> [ SynSem {
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
                                 }
                             ]
            "that"        -> [ SynSem {
                                 syn = S :/: S,
                                 sem = ty tau (purePP (lam x x))
                                 } ]

--------------------------------------------------------------------------------
-- * Priors and response functions


-- | Prior to be used for the factivity example.
factivityPrior :: Term
factivityPrior = let' x (LogitNormal 0 1) (let' y (LogitNormal 0 1) (let' z (LogitNormal 0 1) (let' b (Bern x) (Return (UpdCG (let' c (Bern y) (let' d (Bern z) (Return (UpdLing (lam x c) (UpdEpi (lam x (lam p d)) _0))))) (UpdTauKnow b ϵ))))))

-- | Respones function to be used for the factivity example.
factivityRespond :: Term -> Term -> Term
factivityRespond = respond (lam x (Truncate (Normal x (Var "sigma")) 0 1))
