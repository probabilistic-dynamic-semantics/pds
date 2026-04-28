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
import Data.List                      (nub)
import Framework.Lambda
import Framework.Grammar
import Theory.Signature

type Distr      = (String, [String])
type VarName    = String
type Bounds     = (Double, Double)
type Params     = [(VarName, Maybe Bounds, Distr)]
type Likelihood = (VarName, Distr)

data StanModel = StanModel { params :: Params, likelihood :: Likelihood }
  deriving (Eq)

makeParams :: Term -> Params
makeParams = \case
  Let vn (LogitNormal m s)           t
    -> (vn, Just (0, 1), ("logit_normal", [show m, show s])) : makeParams t
  Let vn (Normal m s)                t
    -> (vn, Nothing, ("normal", [show m, show s]))           : makeParams t
  Let vn (Uniform (DCon a) (DCon b)) t
    -> (vn, Just (a, b), ("uniform", [show a, show b]))      : makeParams t
  _ -> []

makeLikelihood :: Term -> Likelihood
makeLikelihood = \case
  Let _ _ t -> makeLikelihood t
  (Normal m s) -> ("y", ("normal", [show m, show s]))

makeStanModel :: Term -> StanModel
makeStanModel t = StanModel { params = makeParams t
                            , likelihood = makeLikelihood t
                            }

data Block = Data
           | Functions
           | GeneratedQuantities
           | Model
           | Parameters
           | TransformedData
           | TransformedParameters
  deriving (Eq)

indent :: Int -> String -> String
indent 0 s = s
indent n s = "  " ++ indent (n - 1) s

distrType :: Distr -> String
distrType = \case
  ("bernoulli"  , _) -> "int"
  ("exponential", _) -> "real"
  ("logistic"   , _) -> "real"
  ("normal"     , _) -> "real"
  ("uniform"    , _) -> "real"

functionDefs :: String -> String
functionDefs = \case
  "truncated_normal" -> "\n" ++ indent 1 "real truncated_normal_lpdf" ++
                        "(real x, real mu, real sigma, real a, real b) {\n" ++
                        indent 2 "return normal_lpdf(x | mu, sigma) -\n" ++
                        indent 3 "log_diff_exp(normal_lcdf(b | mu, sigma),\n" ++
                        indent 4 "normal_lcdf(a | mu, sigma));\n" ++
                        indent 1 "}\n"
  _                  -> ""

renderFunctions :: StanModel -> String
renderFunctions (StanModel ps (_, (dLik, _))) = concatMap functionDefs distrs
  where distrs :: [String]
        distrs = nub $ dLik : map (\(_, _, (d, _)) -> d) ps

renderParams :: StanModel -> String
renderParams = \case
  StanModel [] _ -> ""
  StanModel ((vn, Just (l, u), d) : ps) lik
    -> indent 1 (distrType d) ++ "<lower=" ++ show l ++ ", upper=" ++ show u ++
       "> " ++ vn ++ ";\n" ++ renderParams (StanModel ps lik)
  StanModel ((vn, _          , d) : ps) lik
    -> indent 1 (distrType d) ++ " " ++ vn ++ ";\n" ++
       renderParams (StanModel ps lik)

renderModel :: StanModel -> String
renderModel m = indent 1 "// PRIORS\n\n" ++ renderPriors (params m) ++ "\n\n" ++
                indent 1 "// LIKELIHOOD\n\n" ++ renderLikelihood (likelihood m)
  where renderPriors :: Params -> String
        renderPriors = \case
          [] -> ""
          (vn, _, (name, args)) : ps
            -> indent 1 vn ++ " ∼ " ++ name ++ "(" ++ renderArgs args ++
               ");\n" ++ renderPriors ps
        renderLikelihood :: Likelihood -> String
        renderLikelihood (vn, (name, args)) = indent 1 vn ++ " ∼ " ++ name ++
                                              "(" ++ renderArgs args ++ ");\n"
        renderArgs :: [String] -> String
        renderArgs []             = ""
        renderArgs (a:rgs@(r:gs)) = a ++ ", " ++ renderArgs rgs
        renderArgs (a:rgs)        = a ++ renderArgs rgs

render :: Block -> StanModel -> String
render = \case
  Functions  -> wrapWith "functions"  . renderFunctions
  Model      -> wrapWith "model"      . renderModel
  Parameters -> wrapWith "parameters" . renderParams
  where wrapWith block contents = block ++ " {\n" ++ contents ++ "}"
                  
stan :: Typed -> IO ()
stan t = do putStrLn "Checking type..."
            case typeOf t of
              Nothing -> putStrLn "Your model isn't well-typed!"
              Just ty -> if   ty == P r
                         then putStrLn $ show ty ++ "!\nYour Stan model:\n\n" ++
                              render Functions  m ++ "\n\n" ++
                              render Parameters m ++ "\n\n" ++
                              render Model      m
                         else putStrLn $ "The type of your model is" ++
                              show ty ++ ", not P r!"
  where m = makeStanModel (termOf t)
