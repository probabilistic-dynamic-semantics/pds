{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

{-|
Module      : Framework.Lambda.Convenience
Description : Convenience functions, etc.
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com

Convenience functions, smart constructors, etc.
-}

module Framework.Lambda.Convenience where

import Control.Applicative
import Framework.Lambda.Terms
import Framework.Lambda.Types

--------------------------------------------------------------------------------
-- * Convenience functions, smart constructors, etc.

-- ** Type abbreviations.

α, β, ι, κ, σ, e, t, r :: Type
α = TyVar "α"
β = TyVar "β"
ι = TyVar "ι"
ω = TyVar "ω"
κ = TyVar "κ"
σ = TyVar "σ"
e = Atom "e" 
t = Atom "t"
r = Atom "r"

q, popQ :: Type -> Type -> Type -> Type
q    i q a = TyCon "Q"    [i, q, a]
popQ i q a = TyCon "popQ" [i, q, a]

pattern SCon :: String -> Term
pattern SCon x = Con (Left x)

pattern DCon :: Double -> Term
pattern DCon x = Con (Right x)

pattern Fa, GetPP, One, Zero, Tr, Undefined :: Term
pattern Fa        = SCon "F"
pattern GetPP     = Lam "s" (Return (Var "s" `Pair` Var "s"))
pattern One       = DCon 1
pattern Zero      = DCon 0
pattern Tr        = SCon "T"
pattern Undefined = SCon "#"

pattern Bern, CG, Factor, Indi, Neg, Height, DTall, Observe, Pr, Epi, SocPla :: Term -> Term
pattern Bern p    = SCon "Bernoulli" `App` p
pattern CG s      = SCon "CG" `App` s
pattern Factor x  = SCon "factor" `App` x
pattern Indi p    = SCon "𝟙" `App` p
pattern Max pred  = SCon "max" `App` pred
pattern Neg x     = SCon "neg" `App` x
pattern Epi i     = SCon "epi" `App` i
pattern TauKnow s = SCon "tau_know" `App` s
pattern Ling i    = SCon "ling" `App` i
pattern Phil i    = SCon "phil" `App` i
pattern Height i  = SCon "height" `App` i
pattern DTall s   = SCon "d_tall" `App` s
pattern SocPla i  = SCon "soc_pla" `App` i
pattern Observe p = SCon "observe" `App` p
pattern Pr t      = SCon "Pr" `App` t
pattern Prop1 i   = SCon "prop1" `App` i
pattern PopQUD s  = SCon "pop_QUD" `App` s

pattern Add, And, Eq, GE, Mult, Normal, Or, UpdEpi, UpdCG, UpdHeight, UpdDTall, UpdSocPla, UpdProp1, PushQUD :: Term -> Term -> Term
pattern Add x y         = SCon "add" `App` (Pair x y)
pattern And p q         = SCon "(∧)" `App` p `App` q
pattern Or p q          = SCon "(∨)" `App` p `App` q
pattern Eq x y          = SCon "(=)" `App` (Pair x y)
pattern GE a b          = SCon "(≥)" `App` a `App` b
pattern Mult x y        = SCon "mult" `App` (Pair x y)
pattern Beta x y        = SCon "Beta" `App` (Pair x y)
pattern Normal x y      = SCon "Normal" `App` (Pair x y)
pattern LogitNormal x y = SCon "Logit_normal" `App` (Pair x y)
pattern UpdEpi acc i    = SCon "upd_epi" `App` acc `App` i
pattern UpdCG cg s      = SCon "upd_CG" `App` cg `App` s
pattern UpdLing p i     = SCon "upd_ling" `App` p `App` i
pattern UpdTauKnow b s  = SCon "upd_tau_know" `App` b `App` s
pattern UpdHeight p i   = SCon "upd_height" `App` p `App` i
pattern UpdDTall d s    = SCon "upd_d_tall" `App` d `App` s
pattern UpdSocPla p i   = SCon "upd_soc_pla" `App` p `App` i
pattern UpdProp1 b i    = SCon "upd_prop1" `App` b `App` i
pattern PushQUD q s     = SCon "push_QUD" `App` q ` App` s

pattern Disj, ITE, Truncate :: Term -> Term -> Term -> Term
pattern Disj x m n      = SCon "disj" `App` (Pair (Pair x m) n)
pattern ITE p x y       = SCon "if_then_else" `App` (Pair (Pair p x) y)
pattern Truncate m x y  = SCon "Truncate" `App` (Pair x y) `App` m
pattern NormalCDF x y z = SCon "Normal_cdf" `App` (Pair x y) `App` z

pattern NormalCDF' v v' x y t = Pr (Let v (Normal x y) (Return (GE t (Var v'))))

pattern LkUp :: String -> Term -> Term
pattern LkUp c s = SCon c `App` s

pattern Upd :: String -> Term -> Term -> Term
pattern Upd c v s = SCon ('u' : 'p' : 'd' : '_' : c) `App` v `App` s

pattern Pop :: String -> Term -> Term
pattern Pop c s = SCon ('p' : 'o' : 'p' : '_' : c) `App` s

pattern Push :: String -> Term -> Term -> Term
pattern Push c v s = SCon ('p' : 'u' : 's' : 'h' : '_' : c) `App` v `App` s

-- *** Convenience and smart constructors

getPP, a, b, c, d, i, k, m, n, p, s, u, v, w, x, y, z, _' :: Term
a  = Var "a"
b  = Var "b"
c  = Var "c"
d  = Var "d"
i  = Var "i"
k  = Var "k"
m  = Var "m"
n  = Var "n"
p  = Var "p"
s  = Var "s"
u  = Var "u"
v  = Var "v"
w  = Var "w"
x  = Var "x"
y  = Var "y"
z  = Var "z"
_' = Var "_"

_0, ϵ, prop1, prop2 :: Term
_0    = sCon "@"
ϵ     = sCon "ϵ"
prop1 = sCon "prop1"
prop2 = sCon "prop2"

getPP = lam s (Return (s & s))

epi, cg, factor, observe, normalL, max', purePP, putPP, pr :: Term -> Term
assert φ       = φ >>>= lam p (getPP >>>= lam s ((purePP (cg s)) >>>= lam c (putPP (upd_CG (let' i c (let' _' (observe (p @@ i)) (Return i))) s))))
ask κ          = κ >>>= Lam "q" (getPP >>>= Lam "s" ((putPP (push_QUD (Var "q") (Var "s")))))
epi i          = sCon "epi" @@ i
cg s           = sCon "CG" @@ s
upd_CG cg s    = sCon "upd_CG" @@ cg @@ s
pop_qud s      = sCon "pop_QUD" @@ s
push_QUD q s   = sCon "push_QUD" @@ q @@ s
factor x       = sCon "factor" @@ x
ling i         = sCon "ling" @@ i
phil i         = sCon "phil" @@ i
max' pred      = sCon "max" @@ pred
normalL x      = normal x (sCon "σ")
observe x      = sCon "observe" @@ x
purePP t       = Lam fr (Return (t & Var fr))
  where fr:esh = fresh [t]
putPP s        = Lam fr (Return (TT & s))
  where fr:esh = fresh [s]
pr t           = sCon "Pr" @@ t

(>>>=), (<**>), (<$$>), lam, normal :: Term -> Term -> Term
t >>>= u    = lam fr (let' e (t @@ fr) (u @@ Pi1 e @@ Pi2 e))
  where fr:e:sh = map Var $ fresh [t, u]
m >>> n     = m >>>= (lam _' n)
t <**> u    = t >>>= (lam fr (u >>>= (lam e (purePP (fr @@ e)))))
  where fr:e:sh = map Var $ fresh [t, u]
t <$$> u    = purePP t Framework.Lambda.Convenience.<**> u
lam (Var v) = Lam v
normal x y  = sCon "Normal" @@ (x & y)

let', respond :: Term -> Term -> Term -> Term
let' (Var v)   = Let v
respond f bg m = let' s bg m'
  where m'     = let' _s' (m @@ s) (let' i (cg (Pi2 _s')) (f @@ max' (lam x (Pi1 (pop_qud (Pi2 _s')) @@ x @@ i))))
        s:_s':i:x:_ = map Var $ fresh [bg, m]

-- | 'Num' instance for 'Term', just as a notational convenience.
instance Num Term where
  t * u           = case (t, u) of
                      (DCon x, DCon y) -> DCon (x * y)
                      _                -> sCon "mult"  @@ (t & u)
  t + u           = case (t, u) of
                      (DCon x, DCon y) -> DCon (x + y)
                      _                -> sCon "add" @@ (t & u)
  negate t        = sCon "neg"   @@ t
  fromInteger x   = dCon (fromInteger x)
  signum (DCon x) = DCon (signum x)
  abs (DCon x)    = DCon (abs x)

-- *** Generic functions

-- | Compute entailments.
entails :: Term -> Term -> Bool
entails p q         | p == q = True
entails p (And q r)          = entails p q && entails p r
entails p (Or q r)           = entails p q || entails p r
entails (And p q) r          = entails p r || entails q r
entails (Or p q) r           = entails p r && entails q r
entails _ _                  = False

-- | Collect up constants appearing in some term.
cons :: Term -> [Constant]
cons = \case
  Var v     -> []
  Con c     -> [c]
  Lam v t   -> cons t
  App t u   -> cons t ++ cons u
  TT        -> []
  Pair t u  -> cons t ++ cons u
  Pi1 t     -> cons t
  Pi2 t     -> cons t
  Let v t u -> cons t ++ cons u
  Return t  -> cons t

-- | True of probabilistic programs that only sample, i.e., do not perform
-- inference.
sampleOnly :: Term -> Bool
sampleOnly = \case
  Bern _          -> True
  Normal _ _      -> True
  LogitNormal _ _ -> True
  Truncate _ _ _  -> True
  _               -> False


-- ** Combining signatures and rules

(<||>) :: Alternative m => (a -> m b) -> (a -> m b) -> a -> m b
f <||> g = \x -> f x <|> g x
