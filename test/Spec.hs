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
import Test.Hspec

main :: IO ()
-- main = pure ()
main = hspec $ do
  describe "factivityExample" $ do
    it "yields the appropriate Stan model" $ do
      stanOutput factivityExample `shouldBe` (factivityResult :: Model)

  describe "scaleNormingExample" $ do
    it "yields the appropriate Stan model" $ do
      stanOutput scaleNormingExample `shouldBe` (scaleNormingResult :: Model)

  describe "likelihoodExample" $ do
    it "yields the appropriate Stan model" $ do
      stanOutput likelihoodExample `shouldBe` (likelihoodResult :: Model)

getSemantics :: forall (p :: Project). Interpretation p SynSem => Int -> [String] -> Typed
getSemantics n = sem . (indices !! n) . getList . flip (interpretations @p) 0
  where indices = head : map (\f -> f . tail) indices
stanOutput     = fst . runWriter . toStan . termOf

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
