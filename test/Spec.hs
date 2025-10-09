{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Analysis.Adjectives.Adjectives
import Analysis.Adjectives.Signature
import Analysis.Factivity.Factivity
import Analysis.Factivity.Signature
import Control.Monad.Writer
import Framework.Lambda
import Framework.Grammar
import Framework.Target
-- import Test.Hspec

main :: IO ()
main = pure ()
-- main = hspec $ do
  -- describe "factivityExample" $ do
    -- it "yields the appropriate Stan model" $ do
      -- stanOutput factivityExample `shouldBe` (factivityResult :: Model)

  -- describe "scaleNormingExample" $ do
    -- it "yields the appropriate Stan model" $ do
      -- stanOutput scaleNormingExample `shouldBe` (scaleNormingResult :: Model)

  -- describe "likelihoodExample" $ do
    -- it "yields the appropriate Stan model" $ do
      -- stanOutput likelihoodExample `shouldBe` (likelihoodResult :: Model)

getSemantics :: forall (p :: Project). Interpretation p SynSem => Int -> [String] -> Typed
getSemantics n = sem . (indices !! n) . getList . flip (interpretations @p) 0
  where indices = head : map (\f -> f . tail) indices
stanOutput pp   = Stan (fst (runWriter (toStanParams (termOf pp)))) (fst (runWriter (toStanModel (termOf pp))))

deltaRules = arithmetic <||> states <||> disjunctions <||> cleanUp <||> maxes <||> probabilities <||> logical <||> ite <||> observations
  
s1         = termOf $ getSemantics @Factivity 1 ["jo", "knows", "that", "bo", "is", "a", "linguist"] 
q1         = termOf $ getSemantics @Factivity 1 ["how", "likely", "that", "bo", "is", "a", "linguist"]
discourse  = ty tauFact $ assert s1 >>> ask q1

factivityExample = asTyped tauFact (betaDeltaNormal deltaRules . factivityRespond factivityPrior) discourse

factivityResult :: Model
factivityResult = Model [ ("v", "logit_normal(0.0, 1.0)")
                        , ("w", "logit_normal(0.0, 1.0)")
                        , ("y", "log_mix(v, truncated_normal_lpdf(y | 1.0, sigma, 0.0, 1.0), truncated_normal_lpdf(y | w, sigma, 0.0, 1.0))") ]

s1'        = termOf $ getSemantics @Adjectives 1 ["jo", "is", "a", "soccer player"] 
q1'        = termOf $ getSemantics @Adjectives 0 ["how", "tall", "jo", "is"]
discourse' = ty tauAdj $ assert s1' >>> ask q1'

scaleNormingExample = asTyped tauAdj (betaDeltaNormal deltaRules . adjectivesRespond scaleNormingPrior) discourse'

scaleNormingResult :: Model
scaleNormingResult = Model [ ("w", "normal(0.0, 1.0)")
                           , ("y", "normal_lpdf(y | w, sigma)") ]

q1''        = termOf $ getSemantics @Adjectives 0 ["how", "likely", "that", "jo", "is", "tall"]
discourse'' = ty tauAdj $ assert s1' >>> ask q1''

likelihoodExample = asTyped tauAdj (betaDeltaNormal deltaRules . adjectivesRespond likelihoodPrior) discourse''

likelihoodResult :: Model
likelihoodResult = Model [ ("v", "normal(0.0, 1.0)")
                         , ("y", "normal_lpdf(y | 1.0 - normal_cdf(v, 0.0, 1.0), sigma)") ]

-- >>> ty tauAdj $ push "QUD"
-- λx.λs.[⟨⋄, push_QUD(x)(s)⟩] : (γ → δ → t) → β → P (⋄ × Q δ γ β)

animate = SCon "animate"
jo = SCon "jo"

ex = view "CG" >>>= lam c (
       set "CG" @@ (
         let' i c (
           observe (animate @@ i @@ jo) (
             Return i
           )
         )
       ) >>>
       purePP jo  
     )

joSig :: Sig
joSig = \x ->
  case x of
    Left "jo"      -> Just e
    Left "animate" -> Just (ι :→ e :→ t)

-- >>> ty (tauAdj <||> joLex) ex
-- λu.(v ∼ (λs.[⟨CG(s), s⟩])(u); (λc.λu.(v ∼ (λx.λs.[⟨⋄, upd_CG(x)(s)⟩])((i ∼ c; (observe(animate(i)(jo)); [i])))(u); (λu.λu.[⟨jo, u⟩])(π₁(v))(π₂(v))))(π₁(v))(π₂(v))) : ν → P (e × ν)

assert' = lam m (
            m >>>= lam p (
              view "CG" >>>= lam c (
                set "CG" @@ (
                  let' i c (
                    observe (p @@ i) (
                      Return i
                    )
                  )
                )
              )
            )
          )

-- >>> ty tauAdj $ betaDeltaNormal deltaRules assert'
-- λm.λu.(v ∼ m(u); [⟨⋄, upd_CG((x ∼ CG(π₂(v)); (observe(π₁(v)(x)); [x])))(π₂(v))⟩]) : (β → P (((τ → t) × χ))) → β → P (⋄ × χ)

runLoc, runOrg, ite1 :: Term -> Term -> Term -> Term
runLoc i x y = SCon "run_loc" @@ i @@ x @@ y
runOrg i x y = SCon "run_org" @@ i @@ x @@ y
ite1 b x y = SCon "if_then_else" @@ (b & x & y)
and, race :: Term -> Term -> Term
and x y = SCon "&" @@ x @@ y
race i x = SCon "race" @@ i @@ x
ex1 :: Term -> Term
ex1 f = SCon "∃" @@ f

-- lexRan :: Lexicon SynSem
-- lexRan = \case
--   "ran" -> [ SynSem {
--                syn = Base "s" \\ np // np,
--                sem = ty
--                    view "tau_run" >>>= lam x (
--                    purePP (
--                        lam y (lam z (lam i (ite1 x
--                                             (runLoc i y z)
--                                             (runOrg i y z)
--                                            ) ) ) )
--                    )
--                } ]
--   _
--     -> []

-- >>> :t ite1
-- <interactive>:1:1-4: error: [GHC-88464]
--     Variable not in scope: ite1
--     Suggested fix: Perhaps use ‘ite’ (imported from Framework.Lambda)

ling1 :: Term
ling1 = Con (Left "ling")

lingSig :: Sig
lingSig = \case
  Left "ling" -> Just (e :→ t)
  _           -> Nothing

-- >>> ty lingSig (lam x (x @@ ling1))
-- λx.x(ling) : ((e → t) → β) → β

