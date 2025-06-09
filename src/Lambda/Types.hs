{-# LANGUAGE LambdaCase #-}

{-|
Module      : Lambda.Types
Description : Curry typing with probabilistic types.
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com

Types and type inference are defined. Types feature variables, quantified at the
top level for some limited polymorphism. Constants may also be polymorphic.
-}

module Lambda.Types ( arity
                    , asTyped
                    , Atom(..)
                    , order
                    , Sig
                    , ty
                    , Type(..)
                    , Typed(..)
                    , unify
                    ) where

import Control.Monad.State (evalStateT, get, lift, put, StateT)
import Data.Char           (toLower)
import Lambda.Terms

--------------------------------------------------------------------------------
-- * Types and type inference

-- ** Types

-- *** Definitions

-- | Atomic types for entities, truth values, and real numbers.
data Atom = E | T | R deriving (Eq, Show)

-- | Arrows, products, and probabilistic types, as well as (a) abstract types
-- representing the addition of a new Q, and (b) type variables for encoding
-- polymorphism.
data Type = At Atom
          | Type :→ Type
          | Unit
          | Type :× Type
          | P Type
          | Q Type Type Type
          | TyVar String
  deriving (Eq)

instance Show Type where
  show = \case
    At a                     -> map toLower $ show a
    (a@(_ :→ _) :→ b)        -> "(" ++ show a ++ ") → " ++ show b
    (a :→ b)                 -> show a ++ " → " ++ show b
    Unit                     -> "⋄"
    a@(_ :→ _) :× b@(_ :→ _) -> "((" ++ show a ++ ") × (" ++ show b ++ "))"
    a@(_ :→ _) :× b          -> "((" ++ show a ++ ") × " ++ show b ++ ")"
    a :× b@(_ :→ _)          -> "(" ++ show a ++ " × (" ++ show b ++ "))"
    a :× b                   -> show a ++ " × " ++ show b
    P a@(_ :→ _)             -> "P (" ++ show a ++ ")"
    P a@(_ :× _)             -> "P (" ++ show a ++ ")"
    P a@(P _)                -> "P (" ++ show a ++ ")"
    P a@(Q _ _ _)            -> "P (" ++ show a ++ ")"
    P a                      -> "P " ++ show a
    Q i q a                  -> "Q" ++
                                drop 1 (show (P i)) ++
                                drop 1 (show (P q)) ++
                                drop 1 (show (P a))
    TyVar s                  -> s

infixr 5 :→
infixl 6 :×

arity, order :: Type -> Int
arity (a :→ b)  = arity b + 1
arity _         = 0
order (a :→ b)  = max (order a + 1) (order b)
order (a :× b)  = max (order a) (order b)
order (P a)     = order a
order (Q i q a) = maximum [order i, order q, order a]
order _         = 0
  
-- *** Type inference
  
-- | Lists of type equalities. We use these to find the most general unifier of
-- two principal types.
type Constr = [(Type, Type)]

-- | Arrive at a most general unifier, or fail if none exists.
unify :: Constr -> Maybe Constr
unify cs = do
  (cs', []) <- pass ([], cs)
  if cs' == cs then Just cs else unify cs'
  where
    -- | Make one pass through the whole list.
    pass :: (Constr, Constr) -> Maybe (Constr, Constr)
    pass = \case
      p@(_, [])  -> Just p
      (u1, x:u2) -> do
        (u1', u2') <- step (u1, u2) x
        pass (u1', u2')

    -- | Take one step toward a most general unifier.
    step :: (Constr, Constr) -> (Type, Type) -> Maybe (Constr, Constr)
    step (u1, u2) = \case
      (x, y)              | x == y     -> Just (u1, u2) -- Get rid of trivial equalities.
      (x@(TyVar _), y)    | occurs x y -> Nothing       -- Impredicativity; uh oh!
      eq@(x@(TyVar _), y)              -> Just ( map (substEqs x y) u1 ++ [eq]
                                               , map (substEqs x y) u2 ) -- Substitute.
      (x, TyVar y)                     -> Just (u1 ++ [(TyVar y, x)], u2) -- Swap.
      (At _, _)                        -> Nothing -- We've already handled equalities.
      (x :→ y, z :→ w)                 -> Just (u1 ++ [(x, z), (y, w)], u2) -- Break apart arrows.
      (_ :→ _, _)                      -> Nothing -- No mismatches allowed.
      (Unit, _)                        -> Nothing -- No mismatches allowed.
      (x :× y, z :× w)                 -> Just (u1 ++ [(x, z), (y, w)], u2) -- Break apart products
      (_ :× _, _)                      -> Nothing -- No mismatches allowed.
      (P x, P y)                       -> Just (u1 ++ [(x, y)], u2) -- Break apart @P@.
      (P _, _)                         -> Nothing -- No mismatches allowed.
      (Q i q x, Q j r y)               -> Just (u1 ++ [(i, j), (q, r), (x, y)], u2) -- Break apart @Q@.
      (Q _ _ _, _)                     -> Nothing -- No mismatches allowed.

    -- | Substitute inside equalities.
    substEqs :: Type -> Type -> (Type, Type) -> (Type, Type)
    substEqs x y = \(z, w) -> (substType x y z, substType x y w)

    -- | Substitute inside a type.
    substType :: Type -> Type -> Type -> Type
    substType x y z | z == x = y
    substType x y (z1 :→ z2) = substType x y z1 :→ substType x y z2
    substType x y (z1 :× z2) = substType x y z1 :× substType x y z2
    substType x y (P z)      = P (substType x y z)
    substType x y (Q i q z)  = Q (substType x y i) (substType x y q) (substType x y z)
    substType _ _ z          = z

    -- | Does @x@ occur in @y@?
    occurs :: Type -> Type -> Bool
    occurs x = \case -- List out possible @y@s.
      y :→ z  -> occurs x y || occurs x z
      y :× z  -> occurs x y || occurs x z
      P y     -> occurs x y
      Q i q y -> occurs x i || occurs x q || occurs x y
      y       -> x == y -- The "otherwise" case; namely, @At@, @Unit@, and @TyVar@.

-- | Assign types to constants.
type Sig = Constant -> Maybe Type

type TyVars    = [String]
type VarTyping = String -> Maybe Type
type TVC       = (TyVars, VarTyping, Constr)

-- | Compute the principal type of a term, given a signature.
computeType :: Sig -> Term -> StateT TVC Maybe Type
computeType tau t = do ty <- collectConstraints tau t
                       -- | Get type constraints.
                       (_, _, cs) <- get
                       -- | Find a most general unifier.
                       subst <- lift (unify cs)
                       -- | Use it to substitute.
                       pure (applySubst subst ty)
  where collectConstraints :: Sig -> Term -> StateT TVC Maybe Type
        collectConstraints tau = \case
          Var v -> do
            (ty:pes, f, cs) <- get
            -- | Check if @v@ is already assigned a type by @f@. If not, assign
            -- it a fresh type variable; if so, use the type it is assigned.
            let g :: String -> Maybe Type
                g v' | v' == v = case fv of
                                   Nothing    -> Just (TyVar ty)
                                   x@(Just _) -> x
                g v' | v' /= v = f v'

                types :: TyVars
                types = case fv of
                          Just _  -> ty:pes
                          Nothing -> pes
                
                fv :: Maybe Type
                fv = f v
            put (types, g, cs)
            lift (g v) -- Return the (possibly new) type assigned to @v@.
          Con c -> do
            (types, f, cs) <- get
            cType <- lift (tau c)
            -- | Ensure that the type variables used for polymorphic constants
            -- are fresh (to prevent any potential clashes), and unify them with
            -- the original type variables.
            let newVars = take lng types'
                rest = drop lng types'
                types' = filter (`notElem` getVars cType) types
                lng = length (getVars cType)
                conCs = zip (TyVar <$> getVars cType) (TyVar <$> newVars)
            put (rest, f, cs)
            subst <- lift (unify conCs) 
            pure (applySubst subst cType)
          App t u -> do
            -- | Process the argument type; process the function type; then
            -- constrain them to be consistent.
            uType <- collectConstraints tau u
            tType <- collectConstraints tau t
            (ty:pes, f, cs) <- get
            put (pes, f, cs ++ [(uType :→ TyVar ty, tType)])
            pure (TyVar ty)
          Lam v t -> do
            -- | Get rid of any type assignments to the abstracted variable
            -- while the body of the abstraction is processed.
            (ty:pes, f, cs) <- get
            let g :: VarTyping
                g v' | v' == v = Just (TyVar ty)
                g v' | v' /= v = f v'
            put (pes, g, cs)
            tType <- collectConstraints tau t
            (types, h, cs') <- get
            newTy <- lift (g v)
            -- | Revert the outgoing variable-typing scheme to the original one
            -- after typing the abstration.
            let i :: VarTyping
                i v' | v' == v = f v'
                i v' | v' /= v = h v'
            put (types, i, cs')
            pure (newTy :→ tType)
          TT -> pure Unit
          Pi1 t -> do
            tType <- collectConstraints tau t
            (t:y:pes, f, cs) <- get
            put (pes, f , cs ++ [(TyVar t :× TyVar y, tType)])
            pure (TyVar t)
          Pi2 t -> do
            tType <- collectConstraints tau t
            (t:y:pes, f, cs) <- get
            put (pes, f, cs ++ [(TyVar t :× TyVar y, tType)])
            pure (TyVar y)
          Pair t u -> do
            tType <- collectConstraints tau t
            uType <- collectConstraints tau u
            pure (tType :× uType)
          Let v t u -> do
            -- | Get rid of any type assignments to the let-bound variable while
            -- its scope is processed.
            (ty:pes, f, cs) <- get
            let g :: VarTyping
                g v' | v' == v = Just (TyVar ty)
                g v' | v' /= v = f v'
            put (pes, g, cs)
            uType <- collectConstraints tau u
            (types, h, cs') <- get
            newTy <- lift (h v)
            -- | Revert the outgoing variable-typing scheme to the original one
            -- after typing the let-construct.
            let i :: VarTyping
                i v' | v' == v = f v'
                i v' | v' /= v = h v'
            put (types, i, cs')
            tType <- collectConstraints tau t
            (ty':pes', j, cs'') <- get
            put (pes', j, cs'' ++ [(tType, P newTy), (uType, P (TyVar ty'))])
            pure uType
          Return t -> do
            tType <- collectConstraints tau t
            pure (P tType)
        applySubst :: Constr -> Type -> Type
        applySubst s = \case
          a@(At _) -> a
          x :→ y   -> applySubst s x :→ applySubst s y
          Unit     -> Unit
          x :× y   -> applySubst s x :× applySubst s y
          P x      -> P (applySubst s x)
          Q x y z  -> Q (applySubst s x) (applySubst s y) (applySubst s z)
          TyVar v  -> lookUp v s

        lookUp :: String -> Constr -> Type
        lookUp v  []                   = TyVar v
        lookUp v1 ((TyVar v2, t) : s') = if   v2 == v1
                                         then t
                                         else lookUp v1 s'

        getVars :: Type -> TyVars
        getVars (TyVar v) = [v]
        getVars (a :→ b)  = getVars a ++ getVars b
        getVars (a :× b)  = getVars a ++ getVars b
        getVars (P a)     = getVars a
        getVars (Q i q a) = getVars i ++ getVars q ++ getVars a
        getVars _         = []

-- | Typed terms (where not every term has a type).
data Typed = Typed { termOf :: Term, typeOf :: Maybe Type } deriving (Eq)

instance Show Typed where
  show (Typed te (Just ty)) = show te ++ " : " ++ show ty
  show (Typed te Nothing)   = "⌜" ++ show te ++ "⌝ is not assigned a type."

-- | Provide a term along with its principal type, given a signature.
ty :: Sig -> Term -> Typed
ty tau te = Typed te theType
    where theType :: Maybe Type
          theType = evalStateT (computeType tau te) (tyVars, start, empty)

          tyVars :: TyVars
          tyVars = "" : map show ints >>= \i -> map (:i) ['α'..'ω']

          ints :: [Integer]
          ints = 1 : map succ ints

          start :: VarTyping
          start = const Nothing

          empty :: Constr
          empty = []

asTyped :: Sig -> (Term -> Term) -> Typed -> Typed
asTyped tau f = ty tau . f . termOf
