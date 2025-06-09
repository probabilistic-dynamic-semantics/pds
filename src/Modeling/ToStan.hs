{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-|
Module      : Modeling.ToStan
Description : CCG derivations
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com

λ-terms are translated into Stan code.
-}

module Modeling.ToStan where

import Control.Monad.Writer
import Control.Monad.State
import Data.Char                        (toLower)
import Lambda
import Grammar
import Grammar.Lexica.SynSem.Adjectives
import Grammar.Lexica.SynSem.Factivity
import Modeling.Delta

type Distr = String
type Var   = String

data Model = Model { statements :: [(Var, Distr)] } deriving (Eq)

instance Show Model where
  show (Model m) = "model {\n  // FIXED EFFECTS\n" ++ render m ++ "}"
    where render [] = ""
          render [(v, d)]     = " \n  // LIKELIHOOD\n  "  ++
                                "target += " ++ map toLower d ++ ";\n"
          render ((v, d) : s) = "  " ++ v ++ " ~ " ++ map toLower d ++ ";\n" ++ render s

data Error = TypeError deriving (Eq)

instance Show Error where
  show TypeError = "Error: Term does not have type P r!"

lRender :: Var -> Term -> String
lRender v (Truncate (Normal x y) z w) = "truncated_normal_lpdf(" ++ v ++
                                        " | " ++ show x ++ ", " ++ show y ++
                                        ", " ++ show z ++ ", " ++ show w ++ ")"
lRender v (Normal x y) = "normal_lpdf(" ++ v ++
                         " | " ++ show x ++ ", " ++ show y ++ ")"
lRender v (Disj x y z) = "log_mix(" ++ show x ++ ", " ++ lRender v y ++ ", " ++ lRender v z ++ ")" 

pRender :: Term -> String
pRender (Normal x y) = "normal(" ++ show x ++ ", " ++ show y ++ ")"
pRender (LogitNormal x y) = "logit_normal(" ++ show x ++ ", " ++ show y ++ ")"
pRender (Truncate m x y) = pRender m ++ " T[" ++ show x ++ ", " ++ show y ++ "]"

stanRender :: Term -> String
stanRender = \case
  Var x      -> x
  Disj x y z -> "mix(" ++ show x ++ ", " ++ stanRender y ++ ", " ++ stanRender z ++ ")"
  SCon x     -> map toLower x
  DCon x     -> show x
  Pair x y   -> stanRender x ++ ", " ++ stanRender y
  App x y    -> stanRender x ++ "(" ++ stanRender y ++ ")"
  Return x   -> "dirac(" ++ stanRender x ++ ")"

toStan :: Term -> Writer [Error] Model
toStan = \case
  t         | typeOf (ty tau t) /= Just (P (At R)) -> do
      tell [TypeError]
      pure (Model [])
  t@(Let x y z) -> toStan' t
    where toStan' (Let x y z) = do
            yResult <- toStan' y
            case yResult of
              Model ((_, distr) : ys) -> do
                Model zs      <- toStan z
                pure $ Model ((x, distr) : ys ++ zs)
          toStan' result = pure $ Model [("", pRender result)]
  result   -> do
    pure (Model [("y", lRender "y" result)])

getSemantics :: forall (p :: Project). Interpretation p SynSem => Int -> [String] -> Typed
getSemantics n = sem . (indices !! n) . getList . flip (interpretations @p) 0
  where indices = head : map (\f -> f . tail) indices
stanOutput     = fst . runWriter . toStan . termOf
  
s1         = termOf $ getSemantics @Factivity 1 ["jo", "knows", "bo", "is", "a", "linguist"] 
q1         = termOf $ getSemantics @Factivity 1 ["likely", "bo", "is", "a", "linguist"]
discourse  = ty tau $ assert s1 >>> ask q1
deltaRules = arithmetic <||> indices <||> states <||> disjunctions <||> cleanUp <||> maxes <||> probabilities <||> logical <||> ite <||> observations
factivityExample = asTyped tau (betaDeltaNormal deltaRules . respond (lam x (Truncate (Normal x (Var "sigma")) 0 1)) knowPrior) discourse

