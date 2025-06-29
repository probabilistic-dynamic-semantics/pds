{-# LANGUAGE LambdaCase #-}

{-|
Module      : Framework.Grammar.Lexica.SynSem.Convenience
Description : Some convenience functions.
Copyright   : (c) Julian Grove and Aaron Steven White, 2025
License     : MIT
Maintainer  : julian.grove@gmail.com
-}

module Framework.Grammar.Lexica.SynSem.Convenience where

import Framework.Grammar.CCG
import Framework.Grammar.Lexica.SynSem
import Framework.Lambda

--------------------------------------------------------------------------------
-- * Some convenience functions

data PairFun f g a b = PairFun { fST :: f a, sND :: g b } deriving (Eq, Show)

compDepth :: String -> Cat -> Cat -> PairFun Maybe Maybe (Int, Cat) (Int, Cat)
compDepth "r" (c :/: b1) b2                 | b1 == b2
  = PairFun (Just (0, c)) (Just (0, c))
compDepth "r" c1@(c2 :/: a1) b1@(b2 :/: a2) | a1 == a2
  = let x1  = fST $ compDepth "r" c1 b2
        y2  = sND $ compDepth "r" c2 b2
        upd = fmap (\(d, c) -> (d + 1, c :/: a1))
        x1' = upd x1
        y2' = upd y2
    in  PairFun x1' y2'
compDepth "r" c1@(c2 :\: a1) b1@(b2 :\: a2) | a1 == a2
  = let y2  = sND $ compDepth "r" c2 b2
        upd = fmap (\(d, c) -> (d + 1, c :\: a1))
        y2' = upd y2
    in  PairFun Nothing y2'
compDepth "r" c (b :/: a)
  = let x1  = fST $ compDepth "r" c b
        upd = fmap (\(d, c') -> (d + 1, c' :/: a))
        x1' = upd x1
    in  PairFun x1' Nothing
compDepth "r" c (b :\: a)
  = let x1  = fST $ compDepth "r" c b
        upd = fmap (\(d, c') -> (d + 1, c' :\: a))
        x1' = upd x1
    in  PairFun x1' Nothing
compDepth l b2 (c :\: b1)                  | b1 == b2
  = PairFun (Just (0, c)) (Just (0, c))
compDepth l b1@(b2 :\: a2) c1@(c2 :\: a1)  | a1 == a2
  = let x1  = fST $ compDepth l b2 c1
        y2  = sND $ compDepth l b2 c2
        upd = fmap (\(d, c) -> (d + 1, c :/: a1))
        x1' = upd x1
        y2' = upd y2
    in  PairFun x1' y2'
compDepth l b1@(b2 :/: a2) c1@(c2 :/: a1)  | a1 == a2
  = let y2  = sND $ compDepth l b2 c2
        upd = fmap (\(d, c) -> (d + 1, c :\: a1))
        y2' = upd y2
    in  PairFun Nothing y2'
compDepth l (b :/: a) c
  = let x1  = fST $ compDepth l b c
        upd = fmap (\(d, c') -> (d + 1, c' :/: a))
        x1' = upd x1
    in  PairFun x1' Nothing
compDepth l (b :\: a) c
  = let x1  = fST $ compDepth l b c
        upd = fmap (\(d, c') -> (d + 1, c' :\: a))
        x1' = upd x1
    in  PairFun x1' Nothing
compDepth _ _ _
  = PairFun Nothing Nothing

compDepthEnglish :: String -> Cat -> Cat -> PairFun Maybe Maybe (Int, Cat) (Int, Cat)
compDepthEnglish d c1 c2 = let PairFun x y = compDepth d c1 c2
                           in  case x of
                                 Just (n1, _) | n1 > 1 -> case y of
                                                            Just (n2, _) | n2 > 0 -> PairFun Nothing Nothing
                                                            _                     -> PairFun Nothing y
                                 _                     -> case y of
                                                            Just (n2, _) | n2 > 0 -> PairFun x Nothing
                                                            _                     -> PairFun x y

genComp :: [Term]
genComp = Lam "f" (Lam "x" (Var "f" @@ Var "x")) : map (App (Lam "g" (Lam "f" (Lam "x" (Lam "y" (Var "g" @@ Var "f" @@ (Var "x" @@ Var "y"))))))) genComp

genSub :: [Term]
genSub = Lam "f" (Lam "x" (Var "f" @@ Var "x")) : map (App (Lam "g" (Lam "f" (Lam "x" (Lam "y" (Var "g" @@ (Var "f" @@ Var "y") @@ (Var "x" @@ Var "y"))))))) genSub

flipp :: Term -> Term
flipp t = Lam fr (Lam e (t @@ Var e @@ Var fr))
  where fr:e:sh = fresh [t]

combineR (SynSem b x) (SynSem a y)
  = case compDepthEnglish "r" b a of
      PairFun (Just (dComp, cComp)) (Just (dSub, cSub))
        -> [ SynSem cComp (ty tau (betaEtaNormal $ genComp !! dComp <$$> termOf x <**> termOf y))
           , SynSem cSub (ty tau (betaEtaNormal $ genSub !! dSub <$$> termOf x <**> termOf y)) ]
      PairFun (Just (dComp, cComp)) Nothing
        -> [SynSem cComp (ty tau (betaEtaNormal $ genComp !! dComp <$$> termOf x <**> termOf y))]
      PairFun Nothing (Just (dSub, cSub))
        -> [SynSem cSub (ty tau (betaEtaNormal $ genSub !! dSub <$$> termOf x <**> termOf y))]
      _ -> []

combineL (SynSem a x) (SynSem b y)
  = case compDepthEnglish "l" a b of
      PairFun (Just (dComp, cComp)) (Just (dSub, cSub))
        -> [ SynSem cComp (ty tau (betaEtaNormal $ flipp (genComp !! dComp) <$$> termOf x <**> termOf y))
           , SynSem cSub (ty tau (betaEtaNormal $ flipp (genSub !! dSub) <$$> termOf x <**> termOf y)) ]
      PairFun (Just (dComp, cComp)) Nothing
        -> [SynSem cComp (ty tau (betaEtaNormal $ flipp (genComp !! dComp) <$$> termOf x <**> termOf y))]
      PairFun Nothing (Just (dSub, cSub))
        -> [SynSem cSub (ty tau (betaEtaNormal $ flipp (genSub !! dSub) <$$> termOf x <**> termOf y))]
      _ -> []
