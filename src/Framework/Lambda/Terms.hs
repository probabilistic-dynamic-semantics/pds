{-# LANGUAGE LambdaCase #-}

{-|
Module      : Framework.Lambda.Terms
Description : λ-calculus (with probabilistic programs).
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com

We encode (untyped) λ-calculus, with constants, and including a definition of
probabilistic programs.
-}

module Framework.Lambda.Terms ( betaDeltaNormal
                              , betaEtaNormal
                              , betaNormal
                              , Constant
                              , dCon
                              , DeltaRule
                              , etaNormal
                              , freeVars
                              , fresh
                              , sCon
                              , subst
                              , Term(..)
                              , (@@)
                              , (&)
                              ) where

import Control.Monad.State (evalStateT, get, lift, put, StateT)
import Data.Char           (toLower)

--------------------------------------------------------------------------------
-- * Untyped λ-terms

-- ** Terms

-- *** Definitions

-- | Constants are indexed by either strings or real numbers.
type Constant = Either String Double

-- | Variable names are represented by strings.
type VarName = String

teVars :: [VarName]
teVars = "" : map show ints >>= \i -> map (:i) ['u'..'z']
  where ints :: [Integer]
        ints = 1 : map succ ints

-- | Untyped λ-terms. Types are assigned separately (i.e., "extrinsically").
data Term = Var VarName           -- Variables.
          | Con Constant          -- Constants.
          | Lam VarName Term      -- Abstractions.
          | App Term Term         -- Applications.
          | TT                    -- The 0-tuple.
          | Pair Term Term        -- Pairing.
          | Pi1 Term              -- First projection.
          | Pi2 Term              -- Second projection.
          | Return Term           -- Construct a degenerate distribution.
          | Let VarName Term Term -- Sample from a distribution and continue.

instance Eq Term where
  x == y = alphaEq teVars (x, y)
    where alphaEq :: [VarName] -> (Term, Term) -> Bool
          alphaEq (n:ns) = \case
            (Var x, Var y)         -> x == y
            (Con x, Con y)         -> x == y
            (Lam x t, Lam y u)     -> alphaEq ns
                                      ( subst x (Var n) t
                                      , subst y (Var n) u )
            (App t u, App r s)     -> t == r && u == s
            (TT, TT)               -> True
            (Pair t u, Pair r s)   -> t == r && u == s
            (Pi1 t, Pi1 u)         -> t == u
            (Pi2 t, Pi2 u)         -> t == u
            (Return t, Return u)   -> t == u
            (Let x t u, Let y r s) -> t == r &&
                                      alphaEq ns
                                      ( subst x (Var n) u
                                      , subst y (Var n) s )
            _                      -> False

instance Show Term where
  show = \case
    Var v             -> v
    Con (Left s)      -> s
    Con (Right d)     -> show d
    Lam v t           -> "λ" ++ v ++ "." ++ show t
    App t@(Lam _ _) u -> "(" ++ show t ++ ")(" ++ show u ++ ")"
    App t u           -> show t ++ "(" ++ show u ++ ")"
    TT                -> "⋄"
    Pair t u          -> "⟨" ++ show t ++ ", " ++ show u ++ "⟩"
    Pi1 t             -> "π₁(" ++ show t ++ ")"
    Pi2 t             -> "π₂(" ++ show t ++ ")"
    Return t          -> "[" ++ show t ++ "]"
    Let v t u         -> case betaEtaNormal t of
                           Con (Left "factor") `App` _  -> "(" ++ rest
                           Con (Left "observe") `App` _ -> "(" ++ rest
                           _                            -> "(" ++ v ++ " ∼ " ++ rest
                           where rest = show t ++ "; " ++ show u ++ ")"

-- **** Smart-ish constructors

-- | Make arbitrarily typed constants.
sCon :: String -> Term 
sCon s = Con (Left s)

-- | Turn a 'Double' into a constant.
dCon :: Double -> Term
dCon d = Con (Right d)

-- | Abbreviations for application and pairing.
(@@), (&) :: Term -> Term -> Term
t @@ u = App t u
t & u = Pair t u

-- *** Functions, relations on terms

freeVars :: Term -> [VarName]
freeVars = \case
  Var v     -> [v]
  Con _     -> []
  Lam v t   -> filter (/= v) (freeVars t)
  App t u   -> freeVars t ++ freeVars u
  TT        -> []
  Pair t u  -> freeVars t ++ freeVars u
  Pi1 t     -> freeVars t
  Pi2 t     -> freeVars t
  Let v t u -> freeVars t ++ filter (/=v) (freeVars u)
  Return t  -> freeVars t

fresh :: [Term] -> [VarName]
fresh ts = filter (flip notElem (ts >>= freeVars)) teVars

-- | Substitutions.
subst :: VarName -> Term -> Term -> Term
subst x y = \case
  Var v     | v == x   -> y
  Var v     | v /= x   -> Var v
  c@(Con _)            -> c
  Lam v t   | v == x   -> Lam v t
  Lam v t   | v /= x   -> Lam fr (subst x y (subst v (Var fr) t))
    where fr:esh = fresh [t, y, Var x]
  App t u              -> subst x y t @@ subst x y u
  TT                   -> TT
  Pair t u             -> subst x y t & subst x y u
  Pi1 t                -> Pi1 (subst x y t)
  Pi2 t                -> Pi2 (subst x y t)
  Return t             -> Return (subst x y t)
  Let v t u            -> Let fr (subst x y t) (subst x y (subst v (Var fr) u))
    where fr:esh = fresh [u, y, Var x]

-- | The type of Delta rules.
type DeltaRule = Term -> Maybe Term

-- | Beta normal forms, taking delta rules into account.
betaDeltaNormal :: DeltaRule -> Term -> Term
betaDeltaNormal delta = continue . \case
        v@(Var _) -> v
        c@(Con _) -> c
        Lam v t   -> Lam v (bdnd t)
        App t u   -> case bdnd t of
          Lam v t' -> bdnd (subst v u t')
          t'       -> App t' (bdnd u)
        TT        -> TT
        Pair t u  -> Pair (bdnd t) (bdnd u)
        Pi1 t     -> case bdnd t of
                       Pair x _ -> x
                       t'       -> Pi1 t'
        Pi2 t     -> case bdnd t of
                       Pair _ y -> y
                       t'       -> Pi2 t'
        Return t  -> Return (bdnd t)
        Let v t u -> case bdnd t of
                       Return t'  -> bdnd (subst v t' u)
                       Let w t' x -> bdnd (Let fr t'
                                           (Let v (subst w (Var fr) x) u)
                                          )
                         where fr:esh = fresh [u, x]
                       t'         -> Let v t' (bdnd u)
  where continue :: Term -> Term
        continue t = case fmap bdnd (delta t) of
                       Just t' -> t'
                       Nothing -> t

        bdnd :: Term -> Term
        bdnd = betaDeltaNormal delta
        
  
-- | Beta normal forms.
betaNormal :: Term -> Term
betaNormal = betaDeltaNormal (const Nothing)

-- | Eta normal forms.
etaNormal :: Term -> Term
etaNormal = \case
  v@(Var _) -> v
  c@(Con _) -> c
  Lam v t   -> case etaNormal t of
                 App x y | y == Var v && v `notElem` freeVars x -> x
                 t'                                             -> Lam v t'
  App t u   -> etaNormal t @@ etaNormal u
  TT        -> TT
  Pair t u  -> case (etaNormal t, etaNormal u) of
                 (Pi1 t', Pi2 u') | t' == u' -> t'
                 (t', u')                    -> Pair t' u'
  Pi1 t     -> Pi1 (etaNormal t)
  Pi2 t     -> Pi2 (etaNormal t)
  Return t  -> Return (etaNormal t)
  Let v t u -> case etaNormal u of
                 Return u' | u' == Var v -> etaNormal t
                 u'                      -> Let v (etaNormal t) u'

-- | Beta-eta normal forms.
betaEtaNormal :: Term -> Term
betaEtaNormal = etaNormal . betaNormal
