{-# LANGUAGE LambdaCase #-}

{-|
Module      : Framework.Lambda.Types
Description : Curry typing with probabilistic types.
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com

Types and type inference are defined. Types feature variables, quantified at the
top level for some limited polymorphism. Constants may also be polymorphic.
-}

module Framework.Lambda.Types ( arity
                              , asTyped
                              , order
                              , Sig
                              , ty
                              , tyEq
                              , tyEq'
                              , Type(..)
                              , Typed(..)
                              , unify
                              ) where

import Control.Monad.State    (evalStateT, get, lift, put, StateT)
import Data.Char              (toLower)
import Data.List              (nub)
import Framework.Lambda.Terms

--------------------------------------------------------------------------------
-- * Types and type inference

-- ** Types

-- *** Definitions

-- | Arrows, products, and probabilistic types, as well as (a) abstract type
-- constructors, and (b) type variables for encoding polymorphism.
data Type = Atom String
          | Type :→ Type
          | Unit
          | Type :× Type
          | P Type
          | TyCon String [Type]
          | TyVar String
  deriving (Eq)

-- | Relations on types.
type TypeRel = Type -> Type -> Bool

-- | Type-level reductions.
type TypeRed = Type -> Maybe Type

-- | Determine if two types are semantically equivalent, taking type reductions
-- into account.
tyEq :: TypeRed -> TypeRel
tyEq f α β = applySubst substα α' == applySubst substβ β'
  where α', β' :: Type
        α' = applyRed f α
        β' = applyRed f β

        applyRed :: TypeRed -> Type -> Type
        applyRed f ty = case f ty of
                         Just ty' -> applyRed f ty'
                         Nothing  -> descend f ty

        descend :: TypeRed -> Type -> Type
        descend f = \case
          a@(Atom _)  -> a
          ty1 :→ ty2  -> applyRed f ty1 :→ applyRed f ty2
          Unit        -> Unit
          ty1 :× ty2  -> applyRed f ty1 :× applyRed f ty2
          P ty        -> P (applyRed f ty)
          TyCon g tys -> TyCon g (map (applyRed f) tys)
          v@(TyVar _) -> v

        substα, substβ :: Constr
        substα = zip (TyVar <$> αVars) (TyVar <$> newVars)
        substβ = zip (TyVar <$> βVars) (TyVar <$> newVars)
  
        αVars, βVars, newVars :: TyVars
        αVars = getVars α'
        βVars = getVars β'
        newVars = filter (flip notElem $ αVars ++ βVars) tyVars

-- | Match pop types to cancel out the types they pop.
popTy :: TypeRed
popTy = \case
  TyCon ('p' : 'o' : 'p' : f) tys ->
    case last tys of
      TyCon g tys'
        | f == g &&
          length (init tys) == length (init tys') &&
          and (zipWith (==) (init tys) (init tys'))  -> Just (last tys')
      TyCon g tys'
        | otherwise                                  ->
          (\ty -> TyCon g (init tys' ++ [ty])) <$>
          popTy (TyCon ("pop" ++ f) (init tys ++ [last tys']))
  _                               -> Nothing

-- | Semantic type equality, taking popable types into account.
tyEq' :: TypeRel
tyEq' = tyEq popTy

instance Show Type where
  show = \case
    Atom a                   -> a
    (a@(_ :→ _) :→ b)        -> "(" ++ show a ++ ") → " ++ show b
    (a :→ b)                 -> show a ++ " → " ++ show b
    Unit                     -> "⋄"
    a@(_ :→ _) :× b@(_ :→ _) -> "((" ++ show a ++ ") × (" ++ show b ++ "))"
    a@(_ :→ _) :× b          -> "((" ++ show a ++ ") × " ++ show b ++ ")"
    a :× b@(_ :→ _)          -> "(" ++ show a ++ " × (" ++ show b ++ "))"
    a :× b                   -> show a ++ " × " ++ show b
    P a                      -> "P" ++ wrap a
    TyCon f tys              -> f ++ concatMap wrap tys
    TyVar s                  -> s
    where wrap :: Type -> String
          wrap a@(_ :→ _)    = " (" ++ show a ++ ")"
          wrap a@(_ :× _)    = " (" ++ show a ++ ")"
          wrap a@(P _)       = " (" ++ show a ++ ")"
          wrap a@(TyCon _ _) = " (" ++ show a ++ ")"
          wrap a             = " "  ++ show a

infixr 5 :→
infixl 6 :×

arity, order :: Type -> Int
arity (a :→ b)      = arity b + 1
arity _             = 0
order (a :→ b)      = max (order a + 1) (order b)
order (a :× b)      = max (order a) (order b)
order (P a)         = order a
order (TyCon _ tys) = maximum (map order tys)
order _             = 0
  
-- *** Type inference
  
-- | Lists of type equalities. We use these to find the most general unifier of
-- two principal types.
type Constr = [(Type, Type)]

-- | Type variable fs.
tyVars :: TyVars
tyVars = "" : map show ints >>= \i -> map (:i) ['α'..'ω']
  where ints :: [Integer]
        ints = 1 : map succ ints

-- | Get the variable fs that occur in some type.
getVars :: Type -> TyVars
getVars = nub . getVars'
  where getVars' :: Type -> TyVars
        getVars' (TyVar v)     = [v]
        getVars' (a :→ b)      = getVars' a ++ getVars' b
        getVars' (a :× b)      = getVars' a ++ getVars' b
        getVars' (P a)         = getVars' a
        getVars' (TyCon _ tys) = concatMap getVars' tys
        getVars' _             = []

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
      (x@(TyVar _), y)    | occurs x y -> Nothing -- Impredicativity; uh oh!
      eq@(x@(TyVar _), y)              -> Just ( map (substEqs x y) u1 ++ [eq]
                                               , map (substEqs x y) u2 ) -- Substitute.
      (x, TyVar y)                     -> Just (u1 ++ [(TyVar y, x)], u2) -- Swap.
      (Atom _, _)                      -> Nothing -- We've already handled equalities.
      (x :→ y, z :→ w)                 -> Just (u1 ++ [(x, z), (y, w)], u2) -- Break apart arrows.
      (_ :→ _, _)                      -> Nothing -- No mismatches allowed.
      (Unit, _)                        -> Nothing -- No mismatches allowed.
      (x :× y, z :× w)                 -> Just (u1 ++ [(x, z), (y, w)], u2) -- Break apart products
      (_ :× _, _)                      -> Nothing -- No mismatches allowed.
      (P x, P y)                       -> Just (u1 ++ [(x, y)], u2) -- Break apart @P@.
      (P _, _)                         -> Nothing -- No mismatches allowed.
      (TyCon f tys1
        , TyCon g tys2)  | f == g &&
                           length tys1 ==
                           length tys2 -> Just (u1 ++ zip tys1 tys2, u2) -- Break apart @TyCon@.
      (TyCon _ _, _)                   -> Nothing -- No mismatches allowed.

    -- | Substitute inside equalities.
    substEqs :: Type -> Type -> (Type, Type) -> (Type, Type)
    substEqs x y = \(z, w) -> (substType x y z, substType x y w)

    -- | Substitute inside a type.
    substType :: Type -> Type -> Type -> Type
    substType x y z             | z == x = y
    substType x y (z1 :→ z2)             = substType x y z1 :→ substType x y z2
    substType x y (z1 :× z2)             = substType x y z1 :× substType x y z2
    substType x y (P z)                  = P (substType x y z)
    substType x y (TyCon f tys)          = TyCon f (map (substType x y) tys)
    substType _ _ z                      = z

    -- | Does @x@ occur in @y@?
    occurs :: Type -> Type -> Bool
    occurs x = \case -- List out possible @y@s.
      y :→ z      -> occurs x y || occurs x z
      y :× z      -> occurs x y || occurs x z
      P y         -> occurs x y
      TyCon _ tys -> or (map (occurs x) tys)
      y           -> x == y -- The "otherwise" case; fly, @At@, @Unit@, and @TyVar@.

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
                rest    = drop lng types'
                types'  = filter (`notElem` getVars cType) types
                lng     = length (getVars cType)
                conCs   = zip (TyVar <$> getVars cType) (TyVar <$> newVars)
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

-- | Apply a substitution to a type, given a set of constraints.
applySubst :: Constr -> Type -> Type
applySubst s = \case
  a@(Atom _)  -> a
  x :→ y      -> applySubst s x :→ applySubst s y
  Unit        -> Unit
  x :× y      -> applySubst s x :× applySubst s y
  P x         -> P (applySubst s x)
  TyCon f tys -> TyCon f (map (applySubst s) tys)
  TyVar v     -> lookUp v s
    where  lookUp :: String -> Constr -> Type
           lookUp v  []                   = TyVar v
           lookUp v1 ((TyVar v2, t) : s') = if   v2 == v1
                                            then t
                                            else lookUp v1 s'

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
