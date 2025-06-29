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

type Distr   = String
type VarName = String

data Model = Model { statements :: [(VarName, Distr)] } deriving (Eq)

instance Show Model where
  show (Model m) = "model {\n  // FIXED EFFECTS\n" ++ render m ++ "}"
    where render [] = ""
          render [(v, d)]     = " \n  // LIKELIHOOD\n  "  ++
                                "target += " ++ d ++ ";\n"
          render ((v, d) : s) = "  " ++ v ++ " ~ " ++ d ++ ";\n" ++ render s

data Error = TypeError deriving (Eq)

instance Show Error where
  show TypeError = "Error: Term does not have type P r!"

stanShow :: Term -> String
stanShow v@(Var _)         = show v
stanShow x@(DCon _)        = show x
stanShow (NormalCDF x y z) = "normal_cdf(" ++ stanShow z ++ ", " ++ stanShow x ++ ", " ++ stanShow y ++ ")"

lRender :: VarName -> Term -> String
lRender v (Truncate (Normal x y) z w) = "truncated_normal_lpdf(" ++ v ++
                                        " | " ++ show x ++ ", " ++ show y ++
                                        ", " ++ show z ++ ", " ++ show w ++ ")"
lRender v (Normal x y) = "normal_lpdf(" ++ v ++
                         " | " ++ stanShow x ++ ", " ++ stanShow y ++ ")"
lRender v (Disj x y z) = "log_mix(" ++ stanShow x ++ ", " ++ lRender v y ++ ", " ++ lRender v z ++ ")" 

pRender :: Term -> String
pRender (Normal x y) = "normal(" ++ stanShow x ++ ", " ++ stanShow y ++ ")"
pRender (LogitNormal x y) = "logit_normal(" ++ stanShow x ++ ", " ++ stanShow y ++ ")"
pRender (Truncate m x y) = pRender m ++ " T[" ++ stanShow x ++ ", " ++ stanShow y ++ "]"

toStan :: Term -> Writer [Error] Model
toStan = \case
  t         | typeOf (ty tau t) /= Just (P (Atom "r")) -> do
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
