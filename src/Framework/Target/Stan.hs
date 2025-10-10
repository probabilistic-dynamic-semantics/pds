{-# LANGUAGE LambdaCase #-}

{-|
Module      : Framework.Target.Stan
Description : Exports probabilistic programs as Stan code.
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com

Probabilistic programs encoded as λ-terms are translated into Stan code.
-}

module Framework.Target.Stan where

import Analysis.Adjectives.Adjectives
import Analysis.Factivity.Factivity
import Control.Monad.Writer
import Control.Monad.State
import Data.Char                      (toLower)
import Framework.Lambda
import Framework.Grammar
import Theory.Signature

type Distr   = String
type VarName = String

data Params = Params { pars :: [(VarName, Distr)] } deriving (Eq)

instance Show Params where
  show (Params m) = "parameters {\n" ++ render m ++ "}"
    where render []                = ""
          render ((v, bounds) : s) = "  real" ++ bounds ++ " " ++
                                     v ++ ";\n" ++ render s

data Model = Model { statements :: [(VarName, Distr)] } deriving (Eq)

instance Show Model where
  show (Model m) = "model {\n" ++ render m ++ "}"
    where render []           = ""
          render [(v, d)]     = " \n  "  ++
                                "target += " ++ d ++ ";\n"
          render ((v, d) : s) = "  " ++ v ++ " ~ " ++ d ++ ";\n" ++ render s

data Stan = Stan { params :: Params, model :: Model } deriving (Eq)

instance Show Stan where
  show (Stan params model) = show params ++ "\n \n" ++ show model

data Error = TypeError deriving (Eq)

instance Show Error where
  show TypeError = "Error: Term does not have type P r!"

stanShow :: Term -> String
stanShow v@(Var _)         = show v
stanShow x@(DCon _)        = show x
stanShow (NormalCDF x y z) = "normal_cdf(" ++ stanShow z ++ ", " ++
                             stanShow x ++ ", " ++ stanShow y ++ ")"
stanShow (Add x (Neg y))   = stanShow x ++ " - " ++ stanShow y
stanShow (Add x y)         = stanShow x ++ " + " ++ stanShow y
stanShow (Neg x)           = "-" ++ stanShow x

paramsRender :: Term -> String
paramsRender (Normal x y)      = ""
paramsRender (LogitNormal x y) = "<lower=0.0, upper=1.0>"
paramsRender Uniform           = ""
paramsRender (Truncate _ x y)  = "<lower=" ++ stanShow x ++
                                 ", upper=" ++ stanShow y ++ ">"

lRender :: VarName -> Term -> String
lRender v (Truncate (Normal x y) z w) = "truncated_normal_lpdf(" ++ v ++
                                        " | " ++ show x ++ ", " ++ show y ++
                                        ", " ++ show z ++ ", " ++ show w ++ ")"
lRender v (Normal x y)                = "normal_lpdf(" ++ v ++
                                        " | " ++ stanShow x ++ ", " ++
                                        stanShow y ++ ")"
lRender v (Disj x y z)                = "log_mix(" ++ stanShow x ++ ", " ++
                                        lRender v y ++ ", " ++
                                        lRender v z ++ ")" 

pRender :: Term -> String
pRender (Normal x y)           = "normal(" ++ stanShow x ++ ", " ++
                                 stanShow y ++ ")"
pRender (LogitNormal x y)      = "logit_normal(" ++ stanShow x ++ ", " ++
                                 stanShow y ++ ")"
pRender (Truncate m x y)       = pRender m ++ " T[" ++ stanShow x ++ ", " ++
                                 stanShow y ++ "]"
pRender x = error $ show x

toStanParams :: Term -> Writer [Error] Params
toStanParams = \case
  t         | typeOf (ty tau0 t) /= Just (P (Atom "r")) -> do
                tell [TypeError]
                pure (Params [])
  Let x y z -> (\rest -> Params $ (x, paramsRender y) : pars rest) <$>
                   toStanParams z
  _ -> pure (Params [])

toStanModel :: Term -> Writer [Error] Model
toStanModel = \case
  t         | typeOf (ty tau0 t) /= Just (P (Atom "r")) -> do
                tell [TypeError]
                pure (Model [])
  Let _ Uniform z                                       -> toStanModel z
  Let _ (Truncate Uniform _ _) z                        -> toStanModel z
  t@(Let _ _ _)                                         -> toStanModel' t
    where toStanModel' (Let x y z) = do
            yResult <- toStanModel' y
            case yResult of
              Model ((_, distr) : ys) -> do
                Model zs      <- toStanModel z
                pure $ Model ((x, distr) : ys ++ zs)
          toStanModel' result = pure $ Model [("", pRender result)]
  result                                                -> do
    pure (Model [("y", lRender "y" result)])


-- >>> Truncate Uniform 0 1
-- Truncate(⟨0.0, 1.0⟩)(Uniform)
