{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

{-|
Module      : Lambda.Convenience
Description : Convenience functions, etc.
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com

Convenience functions, smart constructors, etc.
-}

module Lambda.Convenience where

import Lambda.Terms
import Lambda.Types

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
e = At E 
t = At T
r = At R

-- ** Signatures

-- | An example signature.
tau :: Sig
tau = \case
  Left  "∀"            -> Just ((α :→ t) :→ t)
  Left  "∃"            -> Just ((α :→ t) :→ t)
  Left  "(∧)"          -> Just (t :→ t :→ t)
  Left  "(∨)"          -> Just (t :→ t :→ t)
  Left  "(⇒)"          -> Just (t :→ t :→ t)
  Left  "¬"            -> Just (t :→ t)
  Left  "T"            -> Just t
  Left  "F"            -> Just t
  Left  "if_then_else" -> Just (t :→ α :× α :→ α)
  Left  "(=)"          -> Just (α :× α :→ t)
  Left  "@"            -> Just ι -- Blank starting world.
  Left  "ϵ"            -> Just σ -- Blank starting state.
  Left  "upd_ling"     -> Just ((e :→ t) :→ ι :→ ι)
  Left  "ling"         -> Just (ι :→ e :→ t)
  Left  "phil"         -> Just (ι :→ e :→ t)
  Left  "upd_soc_pla"  -> Just ((e :→ r) :→ ι :→ ι)
  Left  "soc_pla"      -> Just (ι :→ e :→ t)
  Left  "sleep"        -> Just (ι :→ e :→ t)
  Left  "like"         -> Just (ι :→ e :→ e :→ t)
  Left  "love"         -> Just (ι :→ e :→ e :→ t)
  Left  "j"            -> Just e
  Left  "b"            -> Just e
  Left  "Bernoulli"    -> Just (r :→ P t)
  Left  "Normal"       -> Just (r :× r :→ P r)
  Left  "Truncate"     -> Just (r :× r :→ P r :→ P r)
  Left  "upd_tall"     -> Just ((e :→ r) :→ ι :→ ι)
  Left  "tall"         -> Just (ι :→ e :→ r)
  Left  "(≥)"          -> Just (r :→ r :→ t)
  Left  "disj"         -> Just (r :→ P α :× P α :→ P α)
  Left  "mult"         -> Just (r :× r :→ r)
  Left  "add"          -> Just (r :× r :→ r)
  Left  "neg"          -> Just (r :→ r)
  Left  "#"            -> Just (P α)
  Left  "𝟙"            -> Just (t :→ r)
  Left  "𝔼"            -> Just ((α :→ r) :→ P α :→ r)
  Left  "Pr"           -> Just (P t :→ r)
  Left  "factor"       -> Just (r :→ P Unit)
  Left  "observe"      -> Just (t :→ P Unit)
  Left  "upd_tau_know" -> Just (t :→ σ :→ σ)
  Left  "tau_know"     -> Just (σ :→ t)
  Left  "upd_CG"       -> Just (P ι :→ σ :→ σ)
  Left  "CG"           -> Just (σ :→ P ι)
  Left  "upd_QUD"      -> Just ((κ :→ ι :→ t) :→ σ :→ Q ι κ σ)
  Left  "QUD"          -> Just (Q ι κ σ :→ κ :→ ι :→ t)
  Left  "upd_epi"      -> Just ((e :→ (ω :→ t) :→ t) :→ ι :→ ι)
  Left  "epi"          -> Just (ι :→ e :→ (ω :→ t) :→ t)
  Left  "max"          -> Just ((r :→ t) :→ r)
  Left  "σ"            -> Just r
  Left  _              -> Nothing
  Right _              -> Just r

-- ** Pattern synonyms and term abbreviations

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

pattern Bern, CG, Factor, Indi, Neg, Tall, Normal, Observe, Pr, Epi, SocPla :: Term -> Term
pattern Bern p    = SCon "Bernoulli" `App` p
pattern Normal p  = SCon "Normal" `App` p
pattern CG s      = SCon "CG" `App` s
pattern Factor x  = SCon "factor" `App` x
pattern Indi p    = SCon "𝟙" `App` p
pattern Max pred  = SCon "max" `App` pred
pattern Neg x     = SCon "neg" `App` x
pattern Epi i     = SCon "epi" `App` i
pattern TauKnow s = SCon "tau_know" `App` s
pattern Ling i    = SCon "ling" `App` i
pattern Phil i    = SCon "phil" `App` i
pattern Tall i    = SCon "tall" `App` i
pattern SocPla i  = SCon "soc_pla" `App` i
pattern Observe p = SCon "observe" `App` p
pattern Pr t      = SCon "Pr" `App` t
pattern Prop1 i   = SCon "prop1" `App` i
pattern QUD s     = SCon "QUD" `App` s

pattern Add, And, Eq, GE, Mult, Or, UpdEpi, UpdCG, UpdTall, UpdSocPla, UpdProp1, UpdQUD :: Term -> Term -> Term
pattern Add x y        = SCon "add" `App` (Pair x y)
pattern And p q        = SCon "(∧)" `App` p `App` q
pattern Or p q = SCon "(∨)" `App` p `App` q
pattern Eq x y         = SCon "(=)" `App` (Pair x y)
pattern GE a b         = SCon "(≥)" `App` a `App` b
pattern Mult x y       = SCon "mult" `App` (Pair x y)
pattern UpdEpi acc i   = SCon "upd_epi" `App` acc `App` i
pattern UpdCG cg s     = SCon "upd_CG" `App` cg `App` s
pattern UpdLing p i    = SCon "upd_ling" `App` p `App` i
pattern UpdTauKnow b s = SCon "upd_tau_know" `App` b `App` s
pattern UpdTall p i    = SCon "upd_tall" `App` p `App` i
pattern UpdSocPla p i  = SCon "upd_soc_pla" `App` p `App` i
pattern UpdProp1 b i   = SCon "upd_prop1" `App` b `App` i
pattern UpdQUD q s     = SCon "upd_QUD" `App` q ` App` s

pattern Disj, ITE :: Term -> Term -> Term -> Term
pattern Disj x m n     = SCon "disj" `App` x `App` (Pair m n)
pattern ITE p x y = SCon "if_then_else" `App` p `App` (Pair x y)

-- *** Convenience and smart constructors

getPP, a, b, c, d, i, k, m, n, p, s, u, v, w, x, y, z, _' :: Term
a = Var "a"
b = Var "b"
c = Var "c"
d = Var "d"
i = Var "i"
k = Var "k"
m = Var "m"
n = Var "n"
p = Var "p"
s = Var "s"
u = Var "u"
v = Var "v"
w = Var "w"
x = Var "x"
y = Var "y"
z = Var "z"
_' = Var "_"

_0, ϵ, prop1, prop2 :: Term
_0    = sCon "@"
ϵ     = sCon "ϵ"
prop1 = sCon "prop1"
prop2 = sCon "prop2"

adjPrior :: Term
adjPrior = Return (upd_CG (let' b (Bern (dCon 0.5)) (let' x (normalL (-1)) (let' y (normalL 1) (Return (UpdTall (lam z (ITE (SocPla j @@ z) x y)) j))))) s)
  where j = UpdSocPla (lam x b) _0

knowPrior :: Term
knowPrior = let' x (Normal (0 & 1)) (let' y (Normal (0 & 1)) (let' z (Normal (0 & 1)) (let' b (Bern x) (Return (UpdCG (let' c (Bern y) (let' d (Bern z) (Return (UpdLing (lam x c) (UpdEpi (lam x (lam p d)) _0))))) (UpdTauKnow b ϵ))))))

getPP = Lam "s" (Return (Var "s" & Var "s"))

epi, cg, factor, observe, normalL, max', purePP, putPP, pr :: Term -> Term
assert φ       = φ >>>= lam p (getPP >>>= lam s ((purePP (cg s)) >>>= lam c (putPP (upd_CG (let' i c (let' _' (observe (p @@ i)) (Return i))) s))))
ask κ          = κ >>>= Lam "q" (getPP >>>= Lam "s" ((putPP (upd_QUD (Var "q") (Var "s")))))
epi i          = sCon "epi" @@ i
cg s           = sCon "CG" @@ s
upd_CG cg s    = sCon "upd_CG" @@ cg @@ s
qud s          = sCon "QUD" @@ s
upd_QUD q s    = sCon "upd_QUD" @@ q @@ s
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
t <$$> u    = purePP t <**> u
lam (Var v) = Lam v
normal x y  = sCon "Normal" @@ (x & y)

let', respond :: Term -> Term -> Term -> Term
let' (Var v)   = Let v
respond f bg m = let' s bg m'
  where m'     = let' _s' (m @@ s) (let' i (cg (Pi2 _s')) (f @@ max' (lam x (qud (Pi2 _s') @@ x @@ i))))
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
  Bern _   -> True
  Normal _ -> True
  _        -> False
