module DebugPops where -- ChatGPT-generated.

import           Control.Applicative        ((<|>))
import           Data.List                  (permutations)
import qualified Framework.Lambda.Delta     as Delta
import           Framework.Lambda.Terms
import           Framework.Lambda.Types
import           Framework.Lambda.Signature (mkStackSig)

rTy, eTy, iTy, tTy, sTy :: Type
rTy = Atom "r"
eTy = Atom "e"
iTy = Atom "ι"
tTy = Atom "t"
sTy = Atom "S"

a, i, s :: Type
a = TyVar "a"
i = TyVar "i"
s = TyVar "s"

qTy, popQTy :: Type -> Type -> Type -> Type
qTy i a s    = TyCon "Q" [i, a, s]
popQTy i a s = TyCon "popQ" [i, a, s]

rStack, popRStack :: Type -> Type
rStack s    = TyCon "R" [s]
popRStack s = TyCon "popR" [s]

testSig :: Sig
testSig c = qSig c <|> rSig c <|> constants c
  where
    qSig = mkStackSig s (qTy i a) (popQTy i a)
             [("QUD", a :→ i :→ tTy)]

    rSig = mkStackSig s rStack popRStack
             [("R", eTy)]

    constants (Left "qReal") =
      Just (QualifiedType [] (rTy :→ iTy :→ tTy))
    constants (Left "qEntity") =
      Just (QualifiedType [] (eTy :→ iTy :→ tTy))
    constants (Left "state") =
      Just (QualifiedType [] sTy)
    constants (Left "entity") =
      Just (QualifiedType [] eTy)
    constants (Left "real") =
      Just (QualifiedType [] rTy)
    constants _ = Nothing

con :: String -> Term
con = Con . Left

pushQ :: Term -> Term -> Term
pushQ q s = App (App (con "push_QUD") q) s

popQ :: Term -> Term
popQ = App (con "pop_QUD")

pushR :: Term -> Term -> Term
pushR x s = App (App (con "push_R") x) s

qReal, qEntity, state, entity, real :: Term
qReal   = con "qReal"
qEntity = con "qEntity"
state   = con "state"
entity  = con "entity"
real    = con "real"

checkType :: String -> Term -> Maybe Type -> IO ()
checkType name term expected = do
  let actual = typeOf (ty testSig term)

      passed = case (actual, expected) of
        (Just (QualifiedType _ x), Just y) ->
          tyEq (const Nothing) x y
        (Nothing, Nothing) -> True
        _ -> False

  putStrLn $ (if passed then "PASS: " else "FAIL: ") ++ name
  putStrLn $ "  Term:     " ++ show term
  putStrLn $ "  Expected: " ++ show expected
  putStrLn $ "  Actual:   " ++ show actual
  putStrLn ""
  
runPopTests :: IO ()
runPopTests = do

  -- 1. Push alone.
  checkType "Push QUD"
    (pushQ qReal state)
    (Just (qTy iTy rTy sTy))

  -- 2. Immediate cancellation.
  checkType "Immediate pop"
    (popQ (pushQ qReal state))
    (Just ((rTy :→ iTy :→ tTy) :× sTy))

  -- 3. Descend through a different stack constructor.
  checkType "Pop through R"
    (popQ (pushR entity (pushQ qReal state)))
    (Just ((rTy :→ iTy :→ tTy) :× rStack sTy))

  -- 4. Two QUDs, with different types.
  checkType "Pop most recent QUD"
    (popQ (pushQ qEntity (pushQ qReal state)))
    (Just ((eTy :→ iTy :→ tTy) :×
           qTy iTy rTy sTy))

  -- 5. Pop twice.
  checkType "Two successive pops"
    (popQ (Pi2 (popQ (pushQ qEntity
                            (pushQ qReal state)))))
    (Just ((rTy :→ iTy :→ tTy) :× sTy))

  -- 6. Delay cancellation through abstraction.
  checkType "Delayed pop"
    (App (Lam "x" (popQ (Var "x")))
         (pushQ qReal state))
    (Just ((rTy :→ iTy :→ tTy) :× sTy))

  -- 7. Use the retrieved QUD.
  checkType "Compatible QUD argument"
    (App (Pi1 (popQ (pushQ qReal state))) real)
    (Just (iTy :→ tTy))

  -- 8. Incompatible argument.
  checkType "Incompatible QUD argument"
    (App (Pi1 (popQ (pushQ qReal state))) entity)
    Nothing

  -- 9. Do not skip a QUD because its type is incompatible.
  checkType "Incompatible top QUD"
    (App (Pi1 (popQ (pushQ qEntity
                          (pushQ qReal state)))) real)
    Nothing

  -- 10. An unresolved pop in a polymorphic function.
  checkType "Unresolved pop"
    (Lam "x" (popQ (Var "x")))
    (Just (s :→ ((a :→ i :→ tTy) :× popQTy i a s)))

runUnifyTests :: IO ()
runUnifyTests = do
  putStrLn "Immediate cancellation:"
  print $ unify
    [ ( TyVar "result"
      , popQTy i a (qTy iTy rTy sTy)
      )
    ]

  putStrLn "Cancellation through R:"
  print $ unify
    [ ( TyVar "result"
      , popQTy i a (rStack (qTy iTy rTy sTy))
      )
    ]

  putStrLn "Delayed cancellation:"
  print $ unify
    [ (TyVar "result", popQTy i a s)
    , (s, qTy iTy rTy sTy)
    ]

  putStrLn "Delayed cancellation against a rigid type:"
  print $ unify
    [ (popQTy i a s, sTy)
    , (s, qTy iTy rTy sTy)
    ]

  putStrLn "Incompatible parameters:"
  print $ unify
    [ ( TyVar "result"
      , popQTy iTy eTy (qTy iTy rTy sTy)
      )
    ]

runDeferredPopTests :: IO ()
runDeferredPopTests = do
  putStrLn "Delayed cancellation, reversed order:"
  print $ unify
    [ (s, qTy iTy rTy sTy)
    , (popQTy i a s, sTy)
    ]

  putStrLn "Delayed cancellation, reversed equality:"
  print $ unify
    [ (sTy, popQTy i a s)
    , (s, qTy iTy rTy sTy)
    ]

  putStrLn "Delayed but incompatible cancellation:"
  print $ unify
    [ (popQTy iTy eTy s, sTy)
    , (s, qTy iTy rTy sTy)
    ]

popR :: Term -> Term
popR = App (con "pop_R")

mixedState :: Term
mixedState =
  pushR entity (
    pushQ qEntity (
      pushR entity (
        pushQ qReal state)))

runMixedStackTests :: IO ()
runMixedStackTests = do

  checkType "Interleaved pushes"
    mixedState
    (Just (rStack (qTy iTy eTy
                     (rStack (qTy iTy rTy sTy)))))

  checkType "Pop Q through R"
    (popQ mixedState)
    (Just ((eTy :→ iTy :→ tTy) :×
           rStack (rStack (qTy iTy rTy sTy))))

  checkType "Pop outer R"
    (popR mixedState)
    (Just (eTy :×
           qTy iTy eTy (rStack (qTy iTy rTy sTy))))

  checkType "Pop R through Q"
    (popR (pushQ qReal (pushR entity state)))
    (Just (eTy :× qTy iTy rTy sTy))

  checkType "Successively pop Q and R"
    (popR (Pi2 (popQ mixedState)))
    (Just (eTy :× rStack (qTy iTy rTy sTy)))

  checkType "Successively pop Q, R, Q"
    (popQ (Pi2 (popR (Pi2 (popQ mixedState)))))
    (Just ((rTy :→ iTy :→ tTy) :× rStack sTy))

  checkType "Empty both stacks"
    (Pi2 (popR (Pi2 (popQ (Pi2
      (popR (Pi2 (popQ mixedState))))))))
    (Just sTy)

  checkType "Push again after popping"
    (pushQ qReal (Pi2 (popQ mixedState)))
    (Just (qTy iTy rTy
             (rStack (rStack (qTy iTy rTy sTy)))))


checkUnify :: String -> [(Type, Type)]
                     -> Maybe [(Type, Type)] -> IO ()
checkUnify name cs expected = do
  let results = [(p, unify p) | p <- permutations cs]

      correct Nothing Nothing = True
      correct (Just actual) (Just required) =
        all (\(v, t) -> lookup v actual == Just t) required
      correct _ _ = False

      failures =
        filter (\(_, actual) -> not (correct actual expected))
               results

  putStrLn $ (if null failures then "PASS: " else "FAIL: ")
             ++ name

  putStrLn $ "  Permutations tested: " ++ show (length results)
  putStrLn $ "  Failures: " ++ show (length failures)

  case failures of
    [] -> pure ()
    ((cs', actual):_) -> do
      putStrLn $ "  Constraints: " ++ show cs'
      putStrLn $ "  Expected:    " ++ show expected
      putStrLn $ "  Actual:      " ++ show actual

runComplexUnifyTests :: IO ()
runComplexUnifyTests = do
  let b = TyVar "b"
      j = TyVar "j"
      z = TyVar "z"
      k = TyVar "k"
      result = TyVar "result"

  checkUnify "Multiple delayed substitutions"
    [ (popQTy i a s, sTy)
    , (s, z)
    , (z, qTy iTy rTy sTy)
    ]
    (Just [(i, iTy), (a, rTy)])

  checkUnify "Nested pop constructors"
    [ (result, popQTy i a (popQTy j b s))
    , (s, qTy iTy eTy (qTy iTy rTy sTy))
    ]
    (Just [(i, iTy), (a, rTy),
           (j, iTy), (b, eTy), (result, sTy)])

  checkUnify "Pop through multiple intervening constructors"
    [ (result, popQTy i a s)
    , (s, rStack (rStack (qTy iTy rTy sTy)))
    ]
    (Just [(i, iTy), (a, rTy),
           (result, rStack (rStack sTy))])

  checkUnify "Preserve parameters of intervening constructors"
    [ (result, popQTy i a
        (TyCon "R" [eTy, k, qTy iTy rTy sTy]))
    ]
    (Just [(i, iTy), (a, rTy),
           (result, TyCon "R" [eTy, k, sTy])])

  checkUnify "Two pops of the same state"
    [ (popQTy i a s, sTy)
    , (popQTy j b s, sTy)
    , (s, qTy iTy rTy sTy)
    ]
    (Just [(i, iTy), (a, rTy),
           (j, iTy), (b, rTy)])

  checkUnify "Conflicting pops of the same state"
    [ (popQTy iTy rTy s, sTy)
    , (popQTy iTy eTy s, sTy)
    , (s, qTy iTy rTy sTy)
    ]
    Nothing

  checkUnify "Pop inside an arrow type"
    [ (popQTy i a s :→ tTy, sTy :→ tTy)
    , (s, qTy iTy rTy sTy)
    ]
    (Just [(i, iTy), (a, rTy)])

  checkUnify "Pop inside a graded type"
    [ (P (popQTy i a s), P sTy)
    , (s, qTy iTy rTy sTy)
    ]
    (Just [(i, iTy), (a, rTy)])

  checkUnify "Pop cancellation before occurs check"
    [ (s, popQTy iTy rTy (qTy iTy rTy s)) ]
    (Just [])


runHigherOrderPopTests :: IO ()
runHigherOrderPopTests = do
  let x = Var "x"
      f = Var "f"

  checkType "Abstract over state, retrieve QUD"
    (App
      (Lam "x" (Pi1 (popQ x)))
      (pushQ qReal state))
    (Just (rTy :→ iTy :→ tTy))

  checkType "Abstract over state, retrieve remainder"
    (App
      (Lam "x" (Pi2 (popQ x)))
      (pushQ qReal state))
    (Just sTy)

  checkType "Higher-order application of pop function"
    (App
      (Lam "f" (App f (pushQ qReal state)))
      (Lam "x" (popQ x)))
    (Just ((rTy :→ iTy :→ tTy) :× sTy))

  checkType "Abstract over pushed QUD"
    (Lam "x" (popQ (pushQ x state)))
    (Just ((a :→ i :→ tTy) :→
           ((a :→ i :→ tTy) :× sTy)))

  checkType "Two uses of the same state"
    (App
      (Lam "x"
        (Pair (Pi1 (popQ x))
              (Pi1 (popQ x))))
      (pushQ qReal state))
    (Just ((rTy :→ iTy :→ tTy) :×
           (rTy :→ iTy :→ tTy)))

  checkType "Incompatible uses of the same state"
    (App
      (Lam "x"
        (Pair
          (App (Pi1 (popQ x)) real)
          (App (Pi1 (popQ x)) entity)))
      (pushQ qReal state))
    Nothing

  checkType "Push and pop through two abstractions"
    (App
      (App
        (Lam "f"
          (Lam "x" (popQ (pushQ f x))))
        qReal)
      state)
    (Just ((rTy :→ iTy :→ tTy) :× sTy))


runOpenPopTests :: IO ()
runOpenPopTests = do

  checkType "Pop through R with unknown tail"
    (Lam "x" (popQ (pushR entity (Var "x"))))
    (Just (s :→ ((a :→ i :→ tTy) :×
                 rStack (popQTy i a s))))

  checkType "Pop Q from empty state"
    (popQ state)
    Nothing

  checkType "Pop Q from state containing only R"
    (popQ (pushR entity state))
    Nothing

  checkType "Pop Q twice from singleton Q stack"
    (popQ (Pi2 (popQ (pushQ qReal state))))
    Nothing

  checkType "Project value from empty pop"
    (Pi1 (popQ state))
    Nothing

  checkType "Incompatible pops of unknown shared state"
    (Lam "x"
      (Pair
        (App (Pi1 (popQ (Var "x"))) real)
        (App (Pi1 (popQ (Var "x"))) entity)))
    Nothing

checkReduction :: String -> Term -> Term -> IO ()
checkReduction name input expected = do
  let result =
        betaDeltaNormalTyped popTy testSig Delta.states
          (ty testSig input)

      expectedType = typeOf (ty testSig expected)

      passed = case (result, expectedType) of
        (Right (Typed actual (Just (QualifiedType _ actualTy))),
         Just (QualifiedType _ expectedTy)) ->
                 actual == expected &&
          tyEq popTy actualTy expectedTy
        _ -> False

  putStrLn $ (if passed then "PASS: " else "FAIL: ")
             ++ name
  putStrLn $ "  Input:    " ++ show (ty testSig input)
  putStrLn $ "  Expected: " ++ show (ty testSig expected)
  putStrLn $ "  Actual:   " ++ show result
  putStrLn ""

runPopReductionTests :: IO ()
runPopReductionTests = do

  checkReduction "Immediate push/pop reduction"
    (popQ (pushQ qReal state))
    (Pair qReal state)

  checkReduction "Reduction through R"
    (popQ (pushR entity (pushQ qReal state)))
    (Pair qReal (pushR entity state))

  checkReduction "Reduction through Q"
    (popR (pushQ qReal (pushR entity state)))
    (Pair entity (pushQ qReal state))

  checkReduction "Reduction of interleaved stacks"
    (popQ mixedState)
    (Pair qEntity
      (pushR entity (pushR entity (pushQ qReal state))))

  checkReduction "Successive reductions"
    (popR (Pi2 (popQ mixedState)))
    (Pair entity (pushR entity (pushQ qReal state)))

  checkReduction "Beta reduction exposes pop redex"
    (App
      (Lam "x" (popQ (Var "x")))
      (pushQ qReal state))
    (Pair qReal state)

  checkReduction "Push/pop reduction with free state"
    (popQ (pushQ qReal (Var "s")))
    (Pair qReal (Var "s"))

  checkReduction "Push/pop reduction under lambda"
    (Lam "x" (popQ (pushQ qReal (Var "x"))))
    (Lam "x" (Pair qReal (Var "x")))

  checkReduction "Pop through R with free state"
    (popQ (pushR entity (Var "s")))
    (Pair
      (Pi1 (popQ (Var "s")))
      (pushR entity (Pi2 (popQ (Var "s")))))

  checkReduction "Pop through R under lambda"
    (Lam "x" (popQ (pushR entity (Var "x"))))
    (Lam "x"
      (Pair
        (Pi1 (popQ (Var "x")))
        (pushR entity (Pi2 (popQ (Var "x"))))))

runAllExtendedTests :: IO ()
runAllExtendedTests = do
  runMixedStackTests
  runComplexUnifyTests
  runHigherOrderPopTests
  runOpenPopTests
  runPopReductionTests

runOccursPopTests :: IO ()
runOccursPopTests = do
  let z = TyVar "z"

  putStrLn "Apparent cycle, order 1:"
  print $ unify
    [ (s, popQTy iTy rTy z)
    , (z, qTy iTy rTy s)
    ]

  putStrLn "Apparent cycle, order 2:"
  print $ unify
    [ (z, qTy iTy rTy s)
    , (s, popQTy iTy rTy z)
    ]

  putStrLn "Genuine recursive type:"
  print $ unify
    [ (s, qTy iTy rTy s) ]

  putStrLn "Genuine recursive type involving pop:"
  print $ unify
    [ (s, popQTy iTy rTy (rStack
             (qTy iTy rTy s))) ]


runReflexivePopTests :: IO ()
runReflexivePopTests = do
  let valid = popQTy iTy rTy
                (qTy iTy rTy sTy)

      invalid = popQTy iTy eTy
                  (qTy iTy rTy sTy)

      empty = popQTy iTy rTy sTy

      unresolved = popQTy iTy rTy s

  putStrLn "Identical valid pop types:"
  print $ unify [(valid, valid)]

  putStrLn "Identical incompatible pop types:"
  print $ unify [(invalid, invalid)]

  putStrLn "Identical underflowing pop types:"
  print $ unify [(empty, empty)]

  putStrLn "Identical unresolved pop types:"
  print $ unify [(unresolved, unresolved)]

  putStrLn "Initially unresolved, subsequently underflowing:"
  print $ unify
    [ (unresolved, unresolved)
    , (s, sTy)
    ]

runSharedPathTests :: IO ()
runSharedPathTests = do

  checkType "Same QUD through different access paths"
    (Lam "x"
      (Pair
        (Pi1 (popQ (Var "x")))
        (Pi1 (popQ (pushR entity (Var "x"))))))
    (Just (s :→
      ((a :→ i :→ tTy) :×
       (a :→ i :→ tTy))))

  checkType "Conflicting requirements through R"
    (Lam "x"
      (Pair
        (App (Pi1 (popQ (Var "x"))) real)
        (App
          (Pi1 (popQ (pushR entity (Var "x"))))
          entity)))
    Nothing

  checkType "Conflicting requirements through two Rs"
    (Lam "x"
      (Pair
        (App (Pi1 (popQ (Var "x"))) real)
        (App
          (Pi1 (popQ
            (pushR entity (pushR entity (Var "x")))))
          entity)))
    Nothing

  checkType "Independent QUDs in different states"
    (Lam "x"
      (Lam "y"
        (Pair
          (App (Pi1 (popQ (Var "x"))) real)
          (App (Pi1 (popQ (Var "y"))) entity))))
    (Just
      (s :→ TyVar "s'" :→
        ((i :→ tTy) :×
         (TyVar "i'" :→ tTy))))

  checkType "Different QUDs in the same stack"
    (Lam "x"
      (Pair
        (Pi1 (popQ (pushQ qReal (Var "x"))))
        (Pi1 (popQ (pushQ qEntity (Var "x"))))))
    (Just
      (s :→
        ((rTy :→ iTy :→ tTy) :×
         (eTy :→ iTy :→ tTy))))

probeSig :: Sig
probeSig (Left "needsS") = Just (QualifiedType [] (sTy :→ eTy))
probeSig c = testSig c

needsS :: Term -> Term
needsS = App (con "needsS")

runProbabilisticPopTests :: IO ()
runProbabilisticPopTests = do
  let x = Var "x"
      input = pushQ qReal state
      body = needsS (Pi2 (popQ x))

  putStrLn "Ordinary abstraction:"
  print $ ty probeSig
    (App
      (Lam "x" body)
      input)

  putStrLn "Abstraction with Return:"
  print $ ty probeSig
    (App
      (Lam "x" (Return body))
      input)

  putStrLn "Abstraction with probabilistic Let:"
  print $ ty probeSig
    (App
      (Lam "x"
        (Let "z" (Return TT)
          (Return body)))
      input)

  putStrLn "Pop on a sampled state:"
  print $ ty probeSig
    (Let "x" (Return input)
      (Return (Pi1 (popQ x))))

  putStrLn "Pop on an empty sampled state:"
  print $ ty probeSig
    (Let "x" (Return state)
      (Return (Pi1 (popQ x))))

  putStrLn "Successive probabilistic bindings:"
  print $ ty probeSig
    (Let "x" (Return input)
      (Let "y" (Return (popQ x))
        (Return (Pi1 (Var "y")))))

runSignatureBoundaryTests :: IO ()
runSignatureBoundaryTests = do
  let getter = Lam "x" (Pi1 (popQ (Var "x")))

      getterType = typeOf (ty testSig getter)

      extendedSig (Left "getter") = getterType
      extendedSig c = testSig c

  putStrLn "Inferred getter type:"
  print getterType

  putStrLn "Direct application to valid state:"
  print $ ty testSig
    (App getter (pushQ qReal state))

  putStrLn "Constant application to valid state:"
  print $ ty extendedSig
    (App (con "getter") (pushQ qReal state))

  putStrLn "Direct application to empty state:"
  print $ ty testSig
    (App getter state)

  putStrLn "Constant application to empty state:"
  print $ ty extendedSig
    (App (con "getter") state)

  putStrLn "Direct application to wrong QUD:"
  print $ ty testSig
    (App
      (App getter (pushQ qEntity state))
      real)

  putStrLn "Constant application to wrong QUD:"
  print $ ty extendedSig
    (App
      (App (con "getter") (pushQ qEntity state))
      real)

runDeepPopTests :: IO ()
runDeepPopTests = do
  runOccursPopTests
  runReflexivePopTests
  runSharedPathTests
  runProbabilisticPopTests
  runSignatureBoundaryTests

runGradeTests :: IO ()
runGradeTests = do
  print $ ty testSig
    (Lam "m" (Let "x" (Var "m") (Return (Var "x"))))

  print $ ty testSig
    (Lam "m" (Lam "k"
      (Let "x" (Var "m") (App (Var "k") (Var "x")))))

  print $ ty testSig
    (Lam "m" (Lam "n"
      (Let "x" (Var "m") (Var "n"))))

-- >>> runOccursPopTests
-- Apparent cycle, order 1:
-- Just [(z,Q ι r s)]
-- Apparent cycle, order 2:
-- Just [(z,Q ι r s)]
-- Genuine recursive type:
-- Nothing
-- Genuine recursive type involving pop:
-- Nothing
-- >>> runReflexivePopTests
-- Identical valid pop types:
-- Just []
-- Identical incompatible pop types:
-- Nothing
-- Identical underflowing pop types:
-- Nothing
-- Identical unresolved pop types:
-- Just [(popQ ι r s,popQ ι r s)]
-- Initially unresolved, subsequently underflowing:
-- Nothing
-- >>> runSharedPathTests
-- PASS: Same QUD through different access paths
--   Term:     λx.⟨π₁(pop_QUD(x)), π₁(pop_QUD(push_R(entity)(x)))⟩
--   Expected: Just s → ((a → i → t) × (a → i → t))
--   Actual:   Just β → ((μ → ν → t) × (μ → ν → t))
-- PASS: Conflicting requirements through R
--   Term:     λx.⟨π₁(pop_QUD(x))(real), π₁(pop_QUD(push_R(entity)(x)))(entity)⟩
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Conflicting requirements through two Rs
--   Term:     λx.⟨π₁(pop_QUD(x))(real), π₁(pop_QUD(push_R(entity)(push_R(entity)(x))))(entity)⟩
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Independent QUDs in different states
--   Term:     λx.λy.⟨π₁(pop_QUD(x))(real), π₁(pop_QUD(y))(entity)⟩
--   Expected: Just s → s' → ((i → t) × (i' → t))
--   Actual:   Just γ → κ → ((ε → t) × (μ → t))
-- PASS: Different QUDs in the same stack
--   Term:     λx.⟨π₁(pop_QUD(push_QUD(qReal)(x))), π₁(pop_QUD(push_QUD(qEntity)(x)))⟩
--   Expected: Just s → ((r → ι → t) × (e → ι → t))
--   Actual:   Just α → ((r → ι → t) × (e → ι → t))
-- >>> runProbabilisticPopTests
-- Ordinary abstraction:
-- (λx.needsS(π₂(pop_QUD(x))))(push_QUD(qReal)(state)) : e
-- Abstraction with Return:
-- (λx.[needsS(π₂(pop_QUD(x)))])(push_QUD(qReal)(state)) : P e
-- Abstraction with probabilistic Let:
-- (λx.(z ∼ [⋄]; [needsS(π₂(pop_QUD(x)))]))(push_QUD(qReal)(state)) : P e
-- Pop on a sampled state:
-- (x ∼ [push_QUD(qReal)(state)]; [π₁(pop_QUD(x))]) : P (r → ι → t)
-- Pop on an empty sampled state:
-- ⌜(x ∼ [state]; [π₁(pop_QUD(x))])⌝ is not assigned a type.
-- Successive probabilistic bindings:
-- (x ∼ [push_QUD(qReal)(state)]; (y ∼ [pop_QUD(x)]; [π₁(y)])) : P (r → ι → t)
-- >>> runSignatureBoundaryTests
-- Inferred getter type:
-- Just β → γ → δ → t
-- Direct application to valid state:
-- (λx.π₁(pop_QUD(x)))(push_QUD(qReal)(state)) : r → ι → t
-- Constant application to valid state:
-- getter(push_QUD(qReal)(state)) : η → θ → t
-- Direct application to empty state:
-- ⌜(λx.π₁(pop_QUD(x)))(state)⌝ is not assigned a type.
-- Constant application to empty state:
-- getter(state) : ε → ζ → t
-- Direct application to wrong QUD:
-- ⌜(λx.π₁(pop_QUD(x)))(push_QUD(qEntity)(state))(real)⌝ is not assigned a type.
-- Constant application to wrong QUD:
-- getter(push_QUD(qEntity)(state))(real) : θ → t

runGradeConstraintTests :: IO ()
runGradeConstraintTests = do
  let sig (Left "needsM") =
        Just (QualifiedType [] (M Unit :→ eTy))
      sig (Left "measure") =
        Just (QualifiedType [] (M Unit))
      sig c = testSig c
    
      f = Lam "m" (Lam "n"
            (App (con "needsM")
              (Let "x" (Var "m") (Var "n"))))

      p = Return TT
      m = con "measure"

  putStrLn "Inferred abstraction type:"
  print $ ty sig f

  putStrLn "P + P:"
  print $ ty sig (App (App f p) p)

  putStrLn "P + M:"
  print $ ty sig (App (App f p) m)

  putStrLn "M + P:"
  print $ ty sig (App (App f m) p)

  putStrLn "M + M:"
  print $ ty sig (App (App f m) m)

-- >>> runGradeConstraintTests
-- Inferred abstraction type:
-- λm.λn.needsM((x ∼ m; n)) : G δ γ → G ε ⋄ → e
-- P + P:
-- ⌜(λm.λn.needsM((x ∼ m; n)))([⋄])([⋄])⌝ is not assigned a type.
-- P + M:
-- (λm.λn.needsM((x ∼ m; n)))([⋄])(measure) : e
-- M + P:
-- (λm.λn.needsM((x ∼ m; n)))(measure)([⋄]) : e
-- M + M:
-- (λm.λn.needsM((x ∼ m; n)))(measure)(measure) : e

runGradeUnifyTests :: IO ()
runGradeUnifyTests = do
  let g = TyVar "g"
      h = TyVar "h"
      p = Atom "P"
      m = Atom "M"
      cs = [(TyCon "+" [g, h], m)]

  print $ unify cs
  print $ unify (cs ++ [(g, p)])
  print $ unify (cs ++ [(g, m)])
  print $ unify (cs ++ [(g, p), (h, p)])
  print $ unify (cs ++ [(g, p), (h, m)])
  print $ unify (cs ++ [(g, m), (h, p)])
  print $ unify (cs ++ [(g, m), (h, m)])

-- >>> runGradeUnifyTests
-- Just [(+ g h,M)]
-- Just [(h,M),(g,P)]
-- Just [(g,M)]
-- Nothing
-- Just [(g,P),(h,M)]
-- Just [(g,M),(h,P)]
-- Just [(g,M),(h,M)]

qcPlain :: Type -> Maybe QualifiedType
qcPlain = Just . QualifiedType []

qcCheck :: String -> Sig -> Term -> Maybe Type -> IO ()
qcCheck name sig term expected = do
  let actual = typeOf (ty sig term)

      passed = case (actual, expected) of
        (Nothing, Nothing) -> True
        (Just (QualifiedType [] x), Just y) ->
          tyEq gradePlus x y
        _ -> False

  putStrLn $ (if passed then "PASS: " else "FAIL: ") ++ name
  putStrLn $ "  Term:     " ++ show term
  putStrLn $ "  Expected: " ++ show expected
  putStrLn $ "  Actual:   " ++ show actual
  putStrLn ""

qcG, qcH, qcA, qcP, qcM :: Type
qcG = TyVar "g"
qcH = TyVar "h"
qcA = TyVar "a"
qcP = Atom "P"
qcM = Atom "M"

qcPlus :: Type -> Type -> Type
qcPlus x y = TyCon "+" [x, y]

qcBody :: Type
qcBody = G qcG qcA :→ G qcH Unit :→ eTy

qcSumM :: QualifiedType
qcSumM = QualifiedType
  [(qcPlus qcG qcH, qcM)]
  qcBody

qcSig :: Sig
qcSig (Left "qc_needsM") =
  qcPlain (M Unit :→ eTy)

qcSig (Left "qc_needsP") =
  qcPlain (P Unit :→ eTy)

qcSig (Left "qc_measure") =
  qcPlain (M Unit)

qcSig (Left "qc_identity") =
  qcPlain (qcA :→ qcA)

qcSig (Left "qc_sumM") =
  Just qcSumM

qcSig (Left "qc_unrestricted") =
  qcPlain qcBody

qcSig (Left "qc_firstM") =
  Just (QualifiedType [(qcG, qcM)] qcBody)

qcSig (Left "qc_sumMReversed") =
  Just (QualifiedType
    [(qcPlus qcH qcG, qcM)]
    qcBody)

qcSig c = testSig c

runConstantTypingTests :: IO ()
runConstantTypingTests = do
  let f = con "qc_sumM"
      p = Return TT
      m = con "qc_measure"
      ident = con "qc_identity"

  qcCheck "Monomorphic constant"
    qcSig m
    (Just (M Unit))

  qcCheck "Polymorphic constant"
    qcSig ident
    (Just (qcA :→ qcA))

  qcCheck "Independent polymorphic constant occurrences"
    qcSig
    (Pair (App ident real)
          (App ident entity))
    (Just (rTy :× eTy))

  putStrLn "Qualified constant in isolation:"
  print $ ty qcSig f

  qcCheck "Qualified constant: P + P"
    qcSig (App (App f p) p)
    Nothing

  qcCheck "Qualified constant: P + M"
    qcSig (App (App f p) m)
    (Just eTy)

  qcCheck "Qualified constant: M + P"
    qcSig (App (App f m) p)
    (Just eTy)

  qcCheck "Qualified constant: M + M"
    qcSig (App (App f m) m)
    (Just eTy)

  qcCheck "Partial constant application to P"
    qcSig (App f p)
    (Just (M Unit :→ eTy))

  qcCheck "Partial constant application to M"
    qcSig (App f m)
    (Just (G qcH Unit :→ eTy))

  qcCheck "Independent qualified constant occurrences"
    qcSig
    (Pair
      (App (App f p) m)
      (App (App f m) p))
    (Just (eTy :× eTy))

  qcCheck "One invalid qualified constant occurrence"
    qcSig
    (Pair
      (App (App f p) m)
      (App (App f p) p))
    Nothing

-- >>> runConstantTypingTests

qcHiddenSig :: Sig
qcHiddenSig (Left "qc_hiddenOr") =
  Just (QualifiedType
    [(qcPlus qcG qcH, qcM)]
    (G qcG Unit :→ eTy))

qcHiddenSig (Left "qc_hiddenP") =
  Just (QualifiedType [(qcH, qcP)] eTy)

qcHiddenSig (Left "qc_hiddenM") =
  Just (QualifiedType [(qcH, qcM)] eTy)

qcHiddenSig (Left "qc_hiddenRestricted") =
  Just (QualifiedType
    [(qcPlus qcG qcH, qcM), (qcH, qcP)]
    (G qcG Unit :→ eTy))

qcHiddenSig (Left "qc_impossible") =
  Just (QualifiedType
    [(qcH, qcP), (qcH, qcM)]
    eTy)

qcHiddenSig (Left "qc_hiddenFree") =
  qcPlain (G qcG Unit :→ eTy)

qcHiddenSig c = qcSig c

runHiddenConstantTests :: IO ()
runHiddenConstantTests = do
  let p = Return TT
      m = con "qc_measure"
      f = con "qc_hiddenOr"

  qcCheck "Hidden variable permits P"
    qcHiddenSig
    (App f p)
    (Just eTy)

  qcCheck "Hidden variable permits M"
    qcHiddenSig
    (App f m)
    (Just eTy)

  qcCheck "Restricted hidden variable excludes P"
    qcHiddenSig
    (App (con "qc_hiddenRestricted") p)
    Nothing

  qcCheck "Restricted hidden variable permits M"
    qcHiddenSig
    (App (con "qc_hiddenRestricted") m)
    (Just eTy)

  qcCheck "Independent qualification-only variables"
    qcHiddenSig
    (Pair
      (con "qc_hiddenP")
      (con "qc_hiddenM"))
    (Just (eTy :× eTy))

  qcCheck "Independent hidden variables across applications"
    qcHiddenSig
    (Pair
      (App f p)
      (con "qc_hiddenP"))
    (Just (eTy :× eTy))

  qcCheck "Unsatisfiable constant qualification"
    qcHiddenSig
    (con "qc_impossible")
    Nothing

-- >>> runHiddenConstantTests

runInferredConstantTests :: IO ()
runInferredConstantTests = do
  let definition =
        Lam "m" (Lam "n"
          (App (con "qc_needsM")
            (Let "x" (Var "m") (Var "n"))))

      inferred = typeOf (ty qcSig definition)

      extendedSig (Left "qc_inferred") = inferred
      extendedSig c = qcSig c

      f = con "qc_inferred"
      p = Return TT
      m = con "qc_measure"

  putStrLn "Inferred qualified signature:"
  print inferred

  qcCheck "Inferred constant: P + P"
    extendedSig (App (App f p) p)
    Nothing

  qcCheck "Inferred constant: P + M"
    extendedSig (App (App f p) m)
    (Just eTy)

  qcCheck "Inferred constant: M + P"
    extendedSig (App (App f m) p)
    (Just eTy)

  qcCheck "Inferred constant: M + M"
    extendedSig (App (App f m) m)
    (Just eTy)

  qcCheck "Inferred constant: partial application to P"
    extendedSig (App f p)
    (Just (M Unit :→ eTy))

  qcCheck "Inferred constant: partial application to M"
    extendedSig (App f m)
    (Just (G qcH Unit :→ eTy))

  qcCheck "Independent inferred constant occurrences"
    extendedSig
    (Pair
      (App (App f p) m)
      (App (App f m) p))
    (Just (eTy :× eTy))

-- >>> runInferredConstantTests

qcCheckReduction :: String -> Sig
                 -> String -> String -> Bool -> IO ()
qcCheckReduction name sig source target expected = do
  let rule (Con (Left c))
        | c == source = Just (con target)
      rule _ = Nothing

      input = ty sig (con source)
      output = ty sig (con target)

      actual =
        betaDeltaNormalTyped popTy sig rule input

      passed = case (typeOf input, typeOf output, actual) of
        (Just _, Just _, Right result) ->
          expected && termOf result == con target
        (Just _, Just _, Left _) ->
          not expected
        _ -> False

  putStrLn $ (if passed then "PASS: " else "FAIL: ") ++ name
  putStrLn $ "  Input:    " ++ show input
  putStrLn $ "  Reduct:   " ++ show output
  putStrLn $ "  Actual:   " ++ show actual
  putStrLn ""

runQualifiedPreservationTests :: IO ()
runQualifiedPreservationTests = do

  qcCheckReduction "Weakening qualification"
    qcSig
    "qc_sumM" "qc_unrestricted"
    True

  qcCheckReduction "Strengthening qualification"
    qcSig
    "qc_unrestricted" "qc_sumM"
    False

  qcCheckReduction "First grade M entails sum M"
    qcSig
    "qc_firstM" "qc_sumM"
    True

  qcCheckReduction "Sum M does not entail first grade M"
    qcSig
    "qc_sumM" "qc_firstM"
    False

  qcCheckReduction "Commutativity of qualification"
    qcSig
    "qc_sumM" "qc_sumMReversed"
    True

  qcCheckReduction "Commutativity, reverse direction"
    qcSig
    "qc_sumMReversed" "qc_sumM"
    True

  qcCheckReduction "Hidden variable imposes no restriction"
    qcHiddenSig
    "qc_hiddenOr" "qc_hiddenFree"
    True

  qcCheckReduction "Unrestricted entails existentially satisfiable constraint"
    qcHiddenSig
    "qc_hiddenFree" "qc_hiddenOr"
    True

  qcCheckReduction "Restricted hidden variable weakens"
    qcHiddenSig
    "qc_hiddenRestricted" "qc_hiddenFree"
    True

  qcCheckReduction "Restricted hidden variable strengthens"
    qcHiddenSig
    "qc_hiddenFree" "qc_hiddenRestricted"
    False

-- >>> runQualifiedPreservationTests

qcPopRequirement :: Type
qcPopRequirement = popQTy i a s

qcStackSig :: Sig
qcStackSig (Left "qc_getter") =
  Just (QualifiedType
    [(qcPopRequirement, qcPopRequirement)]
    (s :→ a :→ i :→ tTy))

qcStackSig (Left "qc_unrestrictedGetter") =
  qcPlain (s :→ a :→ i :→ tTy)

qcStackSig c = qcSig c

runQualifiedStackConstantTests :: IO ()
runQualifiedStackConstantTests = do
  let getter = con "qc_getter"

  putStrLn "Qualified getter constant:"
  print $ ty qcStackSig getter

  qcCheck "Qualified constant retrieves real QUD"
    qcStackSig
    (App getter (pushQ qReal state))
    (Just (rTy :→ iTy :→ tTy))

  qcCheck "Qualified constant retrieves entity QUD"
    qcStackSig
    (App getter (pushQ qEntity state))
    (Just (eTy :→ iTy :→ tTy))

  qcCheck "Qualified constant retrieves QUD through R"
    qcStackSig
    (App getter
      (pushR entity (pushQ qReal state)))
    (Just (rTy :→ iTy :→ tTy))

  qcCheck "Qualified constant rejects empty state"
    qcStackSig
    (App getter state)
    Nothing

  qcCheck "Qualified constant rejects incompatible argument"
    qcStackSig
    (App
      (App getter (pushQ qEntity state))
      real)
    Nothing

  qcCheck "Independent qualified getter occurrences"
    qcStackSig
    (Pair
      (App getter (pushQ qReal state))
      (App getter (pushQ qEntity state)))
    (Just
      ((rTy :→ iTy :→ tTy) :×
       (eTy :→ iTy :→ tTy)))

  qcCheck "Conflicting getters of unknown state"
    qcStackSig
    (Lam "x"
      (Pair
        (App (App getter (Var "x")) real)
        (App (App getter (Var "x")) entity)))
    Nothing

-- >>> runQualifiedStackConstantTests

runInferredStackConstantTests :: IO ()
runInferredStackConstantTests = do
  let definition =
        Lam "x" (Pi1 (popQ (Var "x")))

      inferred = typeOf (ty qcSig definition)

      extendedSig (Left "qc_inferredGetter") = inferred
      extendedSig c = qcSig c

      getter = con "qc_inferredGetter"

  putStrLn "Inferred getter qualification:"
  print inferred

  qcCheck "Inferred getter retrieves real QUD"
    extendedSig
    (App getter (pushQ qReal state))
    (Just (rTy :→ iTy :→ tTy))

  qcCheck "Inferred getter retrieves entity QUD"
    extendedSig
    (App getter (pushQ qEntity state))
    (Just (eTy :→ iTy :→ tTy))

  qcCheck "Inferred getter rejects empty state"
    extendedSig
    (App getter state)
    Nothing

  qcCheck "Inferred getter rejects incompatible argument"
    extendedSig
    (App
      (App getter (pushQ qEntity state))
      real)
    Nothing

  qcCheck "Independent inferred getter occurrences"
    extendedSig
    (Pair
      (App getter (pushQ qReal state))
      (App getter (pushQ qEntity state)))
    (Just
      ((rTy :→ iTy :→ tTy) :×
       (eTy :→ iTy :→ tTy)))

-- >>> runInferredStackConstantTests

runStackPreservationTests :: IO ()
runStackPreservationTests = do

  qcCheckReduction "Weakening stack qualification"
    qcStackSig
    "qc_getter" "qc_unrestrictedGetter"
    True

  qcCheckReduction "Strengthening stack qualification"
    qcStackSig
    "qc_unrestrictedGetter" "qc_getter"
    False

-- >>> runStackPreservationTests

runAllNewQualifiedTests :: IO ()
runAllNewQualifiedTests = do
  runConstantTypingTests
  runHiddenConstantTests
  runInferredConstantTests
  runQualifiedPreservationTests
  runQualifiedStackConstantTests
  runInferredStackConstantTests
  runStackPreservationTests

-- >>> runAllNewQualifiedTests
-- PASS: Monomorphic constant
--   Term:     qc_measure
--   Expected: Just M ⋄
--   Actual:   Just M ⋄
-- PASS: Polymorphic constant
--   Term:     qc_identity
--   Expected: Just a → a
--   Actual:   Just α → α
-- PASS: Independent polymorphic constant occurrences
--   Term:     ⟨qc_identity(real), qc_identity(entity)⟩
--   Expected: Just r × e
--   Actual:   Just r × e
-- Qualified constant in isolation:
-- qc_sumM : (+ γ ε ~ M) ⇒ G γ δ → G ε ⋄ → e
-- PASS: Qualified constant: P + P
--   Term:     qc_sumM([⋄])([⋄])
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Qualified constant: P + M
--   Term:     qc_sumM([⋄])(qc_measure)
--   Expected: Just e
--   Actual:   Just e
-- PASS: Qualified constant: M + P
--   Term:     qc_sumM(qc_measure)([⋄])
--   Expected: Just e
--   Actual:   Just e
-- PASS: Qualified constant: M + M
--   Term:     qc_sumM(qc_measure)(qc_measure)
--   Expected: Just e
--   Actual:   Just e
-- PASS: Partial constant application to P
--   Term:     qc_sumM([⋄])
--   Expected: Just M ⋄ → e
--   Actual:   Just M ⋄ → e
-- PASS: Partial constant application to M
--   Term:     qc_sumM(qc_measure)
--   Expected: Just G h ⋄ → e
--   Actual:   Just G ε ⋄ → e
-- PASS: Independent qualified constant occurrences
--   Term:     ⟨qc_sumM([⋄])(qc_measure), qc_sumM(qc_measure)([⋄])⟩
--   Expected: Just e × e
--   Actual:   Just e × e
-- PASS: One invalid qualified constant occurrence
--   Term:     ⟨qc_sumM([⋄])(qc_measure), qc_sumM([⋄])([⋄])⟩
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Hidden variable permits P
--   Term:     qc_hiddenOr([⋄])
--   Expected: Just e
--   Actual:   Just e
-- PASS: Hidden variable permits M
--   Term:     qc_hiddenOr(qc_measure)
--   Expected: Just e
--   Actual:   Just e
-- PASS: Restricted hidden variable excludes P
--   Term:     qc_hiddenRestricted([⋄])
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Restricted hidden variable permits M
--   Term:     qc_hiddenRestricted(qc_measure)
--   Expected: Just e
--   Actual:   Just e
-- PASS: Independent qualification-only variables
--   Term:     ⟨qc_hiddenP, qc_hiddenM⟩
--   Expected: Just e × e
--   Actual:   Just e × e
-- PASS: Independent hidden variables across applications
--   Term:     ⟨qc_hiddenOr([⋄]), qc_hiddenP⟩
--   Expected: Just e × e
--   Actual:   Just e × e
-- PASS: Unsatisfiable constant qualification
--   Term:     qc_impossible
--   Expected: Nothing
--   Actual:   Nothing
-- Inferred qualified signature:
-- Just (+ δ ε ~ M) ⇒ G δ γ → G ε ⋄ → e
-- PASS: Inferred constant: P + P
--   Term:     qc_inferred([⋄])([⋄])
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Inferred constant: P + M
--   Term:     qc_inferred([⋄])(qc_measure)
--   Expected: Just e
--   Actual:   Just e
-- PASS: Inferred constant: M + P
--   Term:     qc_inferred(qc_measure)([⋄])
--   Expected: Just e
--   Actual:   Just e
-- PASS: Inferred constant: M + M
--   Term:     qc_inferred(qc_measure)(qc_measure)
--   Expected: Just e
--   Actual:   Just e
-- PASS: Inferred constant: partial application to P
--   Term:     qc_inferred([⋄])
--   Expected: Just M ⋄ → e
--   Actual:   Just M ⋄ → e
-- PASS: Inferred constant: partial application to M
--   Term:     qc_inferred(qc_measure)
--   Expected: Just G h ⋄ → e
--   Actual:   Just G θ ⋄ → e
-- PASS: Independent inferred constant occurrences
--   Term:     ⟨qc_inferred([⋄])(qc_measure), qc_inferred(qc_measure)([⋄])⟩
--   Expected: Just e × e
--   Actual:   Just e × e
-- PASS: Weakening qualification
--   Input:    qc_sumM : (+ γ ε ~ M) ⇒ G γ δ → G ε ⋄ → e
--   Reduct:   qc_unrestricted : G α β → G γ ⋄ → e
--   Actual:   Right qc_unrestricted : G α β → G γ ⋄ → e
-- PASS: Strengthening qualification
--   Input:    qc_unrestricted : G α β → G γ ⋄ → e
--   Reduct:   qc_sumM : (+ γ ε ~ M) ⇒ G γ δ → G ε ⋄ → e
--   Actual:   Left "Evaluation error: qc_unrestricted : G \945 \946 \8594 G \947 \8900 \8594 e,\nwhile qc_sumM : (+ \947 \949 ~ M) \8658 G \947 \948 \8594 G \949 \8900 \8594 e"
-- PASS: First grade M entails sum M
--   Input:    qc_firstM : M γ → G δ ⋄ → e
--   Reduct:   qc_sumM : (+ γ ε ~ M) ⇒ G γ δ → G ε ⋄ → e
--   Actual:   Right qc_sumM : (+ γ ε ~ M) ⇒ G γ δ → G ε ⋄ → e
-- PASS: Sum M does not entail first grade M
--   Input:    qc_sumM : (+ γ ε ~ M) ⇒ G γ δ → G ε ⋄ → e
--   Reduct:   qc_firstM : M γ → G δ ⋄ → e
--   Actual:   Left "Evaluation error: qc_sumM : (+ \947 \949 ~ M) \8658 G \947 \948 \8594 G \949 \8900 \8594 e,\nwhile qc_firstM : M \947 \8594 G \948 \8900 \8594 e"
-- PASS: Commutativity of qualification
--   Input:    qc_sumM : (+ γ ε ~ M) ⇒ G γ δ → G ε ⋄ → e
--   Reduct:   qc_sumMReversed : (+ ε γ ~ M) ⇒ G γ δ → G ε ⋄ → e
--   Actual:   Right qc_sumMReversed : (+ ε γ ~ M) ⇒ G γ δ → G ε ⋄ → e
-- PASS: Commutativity, reverse direction
--   Input:    qc_sumMReversed : (+ ε γ ~ M) ⇒ G γ δ → G ε ⋄ → e
--   Reduct:   qc_sumM : (+ γ ε ~ M) ⇒ G γ δ → G ε ⋄ → e
--   Actual:   Right qc_sumM : (+ γ ε ~ M) ⇒ G γ δ → G ε ⋄ → e
-- PASS: Hidden variable imposes no restriction
--   Input:    qc_hiddenOr : (+ γ β ~ M) ⇒ G γ ⋄ → e
--   Reduct:   qc_hiddenFree : G α ⋄ → e
--   Actual:   Right qc_hiddenFree : G α ⋄ → e
-- PASS: Unrestricted entails existentially satisfiable constraint
--   Input:    qc_hiddenFree : G α ⋄ → e
--   Reduct:   qc_hiddenOr : (+ γ β ~ M) ⇒ G γ ⋄ → e
--   Actual:   Right qc_hiddenOr : (+ γ β ~ M) ⇒ G γ ⋄ → e
-- PASS: Restricted hidden variable weakens
--   Input:    qc_hiddenRestricted : M ⋄ → e
--   Reduct:   qc_hiddenFree : G α ⋄ → e
--   Actual:   Right qc_hiddenFree : G α ⋄ → e
-- PASS: Restricted hidden variable strengthens
--   Input:    qc_hiddenFree : G α ⋄ → e
--   Reduct:   qc_hiddenRestricted : M ⋄ → e
--   Actual:   Left "Evaluation error: qc_hiddenFree : G \945 \8900 \8594 e,\nwhile qc_hiddenRestricted : M \8900 \8594 e"
-- Qualified getter constant:
-- qc_getter : (popQ ι θ η ~ popQ ι θ η) ⇒ η → θ → ι → t
-- PASS: Qualified constant retrieves real QUD
--   Term:     qc_getter(push_QUD(qReal)(state))
--   Expected: Just r → ι → t
--   Actual:   Just r → ι → t
-- PASS: Qualified constant retrieves entity QUD
--   Term:     qc_getter(push_QUD(qEntity)(state))
--   Expected: Just e → ι → t
--   Actual:   Just e → ι → t
-- PASS: Qualified constant retrieves QUD through R
--   Term:     qc_getter(push_R(entity)(push_QUD(qReal)(state)))
--   Expected: Just r → ι → t
--   Actual:   Just r → ι → t
-- PASS: Qualified constant rejects empty state
--   Term:     qc_getter(state)
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Qualified constant rejects incompatible argument
--   Term:     qc_getter(push_QUD(qEntity)(state))(real)
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Independent qualified getter occurrences
--   Term:     ⟨qc_getter(push_QUD(qReal)(state)), qc_getter(push_QUD(qEntity)(state))⟩
--   Expected: Just ((r → ι → t) × (e → ι → t))
--   Actual:   Just ((r → ι → t) × (e → ι → t))
-- PASS: Conflicting getters of unknown state
--   Term:     λx.⟨qc_getter(x)(real), qc_getter(x)(entity)⟩
--   Expected: Nothing
--   Actual:   Nothing
-- Inferred getter qualification:
-- Just (popQ δ γ β ~ popQ δ γ β) ⇒ β → γ → δ → t
-- PASS: Inferred getter retrieves real QUD
--   Term:     qc_inferredGetter(push_QUD(qReal)(state))
--   Expected: Just r → ι → t
--   Actual:   Just r → ι → t
-- PASS: Inferred getter retrieves entity QUD
--   Term:     qc_inferredGetter(push_QUD(qEntity)(state))
--   Expected: Just e → ι → t
--   Actual:   Just e → ι → t
-- PASS: Inferred getter rejects empty state
--   Term:     qc_inferredGetter(state)
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Inferred getter rejects incompatible argument
--   Term:     qc_inferredGetter(push_QUD(qEntity)(state))(real)
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Independent inferred getter occurrences
--   Term:     ⟨qc_inferredGetter(push_QUD(qReal)(state)), qc_inferredGetter(push_QUD(qEntity)(state))⟩
--   Expected: Just ((r → ι → t) × (e → ι → t))
--   Actual:   Just ((r → ι → t) × (e → ι → t))
-- PASS: Weakening stack qualification
--   Input:    qc_getter : (popQ ι θ η ~ popQ ι θ η) ⇒ η → θ → ι → t
--   Reduct:   qc_unrestrictedGetter : α → β → γ → t
--   Actual:   Right qc_unrestrictedGetter : α → β → γ → t
-- PASS: Strengthening stack qualification
--   Input:    qc_unrestrictedGetter : α → β → γ → t
--   Reduct:   qc_getter : (popQ ι θ η ~ popQ ι θ η) ⇒ η → θ → ι → t
--   Actual:   Left "Evaluation error: qc_unrestrictedGetter : \945 \8594 \946 \8594 \947 \8594 t,\nwhile qc_getter : (popQ \953 \952 \951 ~ popQ \953 \952 \951) \8658 \951 \8594 \952 \8594 \953 \8594 t"

-- >>> runPopTests
-- PASS: Push QUD
--   Term:     push_QUD(qReal)(state)
--   Expected: Just Q ι r S
--   Actual:   Just Q ι r S
-- PASS: Immediate pop
--   Term:     pop_QUD(push_QUD(qReal)(state))
--   Expected: Just ((r → ι → t) × S)
--   Actual:   Just ((r → ι → t) × S)
-- PASS: Pop through R
--   Term:     pop_QUD(push_R(entity)(push_QUD(qReal)(state)))
--   Expected: Just ((r → ι → t) × R S)
--   Actual:   Just ((r → ι → t) × R S)
-- PASS: Pop most recent QUD
--   Term:     pop_QUD(push_QUD(qEntity)(push_QUD(qReal)(state)))
--   Expected: Just ((e → ι → t) × Q ι r S)
--   Actual:   Just ((e → ι → t) × Q ι r S)
-- PASS: Two successive pops
--   Term:     pop_QUD(π₂(pop_QUD(push_QUD(qEntity)(push_QUD(qReal)(state)))))
--   Expected: Just ((r → ι → t) × S)
--   Actual:   Just ((r → ι → t) × S)
-- PASS: Delayed pop
--   Term:     (λx.pop_QUD(x))(push_QUD(qReal)(state))
--   Expected: Just ((r → ι → t) × S)
--   Actual:   Just ((r → ι → t) × S)
-- PASS: Compatible QUD argument
--   Term:     π₁(pop_QUD(push_QUD(qReal)(state)))(real)
--   Expected: Just ι → t
--   Actual:   Just ι → t
-- PASS: Incompatible QUD argument
--   Term:     π₁(pop_QUD(push_QUD(qReal)(state)))(entity)
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Incompatible top QUD
--   Term:     π₁(pop_QUD(push_QUD(qEntity)(push_QUD(qReal)(state))))(real)
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Unresolved pop
--   Term:     λx.pop_QUD(x)
--   Expected: Just s → ((a → i → t) × popQ i a s)
--   Actual:   Just (popQ δ γ β ~ popQ δ γ β) ⟹ β → ((γ → δ → t) × popQ δ γ β)
-- >>> runUnifyTests
-- Immediate cancellation:
-- Just [(i,ι),(a,r),(result,S)]
-- Cancellation through R:
-- Just [(i,ι),(a,r),(result,R S)]
-- Delayed cancellation:
-- Just [(s,Q ι r S),(i,ι),(a,r),(result,S)]
-- Delayed cancellation against a rigid type:
-- Just [(s,Q ι r S),(i,ι),(a,r)]
-- Incompatible parameters:
-- Nothing
-- >>> runDeferredPopTests
-- Delayed cancellation, reversed order:
-- Just [(s,Q ι r S),(i,ι),(a,r)]
-- Delayed cancellation, reversed equality:
-- Just [(s,Q ι r S),(i,ι),(a,r)]
-- Delayed but incompatible cancellation:
-- Nothing
-- >>> runAllExtendedTests
-- PASS: Interleaved pushes
--   Term:     push_R(entity)(push_QUD(qEntity)(push_R(entity)(push_QUD(qReal)(state))))
--   Expected: Just R (Q ι e (R (Q ι r S)))
--   Actual:   Just R (Q ι e (R (Q ι r S)))
-- PASS: Pop Q through R
--   Term:     pop_QUD(push_R(entity)(push_QUD(qEntity)(push_R(entity)(push_QUD(qReal)(state)))))
--   Expected: Just ((e → ι → t) × R (R (Q ι r S)))
--   Actual:   Just ((e → ι → t) × R (R (Q ι r S)))
-- PASS: Pop outer R
--   Term:     pop_R(push_R(entity)(push_QUD(qEntity)(push_R(entity)(push_QUD(qReal)(state)))))
--   Expected: Just e × Q ι e (R (Q ι r S))
--   Actual:   Just e × Q ι e (R (Q ι r S))
-- PASS: Pop R through Q
--   Term:     pop_R(push_QUD(qReal)(push_R(entity)(state)))
--   Expected: Just e × Q ι r S
--   Actual:   Just e × Q ι r S
-- PASS: Successively pop Q and R
--   Term:     pop_R(π₂(pop_QUD(push_R(entity)(push_QUD(qEntity)(push_R(entity)(push_QUD(qReal)(state)))))))
--   Expected: Just e × R (Q ι r S)
--   Actual:   Just e × R (Q ι r S)
-- PASS: Successively pop Q, R, Q
--   Term:     pop_QUD(π₂(pop_R(π₂(pop_QUD(push_R(entity)(push_QUD(qEntity)(push_R(entity)(push_QUD(qReal)(state)))))))))
--   Expected: Just ((r → ι → t) × R S)
--   Actual:   Just ((r → ι → t) × R S)
-- PASS: Empty both stacks
--   Term:     π₂(pop_R(π₂(pop_QUD(π₂(pop_R(π₂(pop_QUD(push_R(entity)(push_QUD(qEntity)(push_R(entity)(push_QUD(qReal)(state))))))))))))
--   Expected: Just S
--   Actual:   Just S
-- PASS: Push again after popping
--   Term:     push_QUD(qReal)(π₂(pop_QUD(push_R(entity)(push_QUD(qEntity)(push_R(entity)(push_QUD(qReal)(state)))))))
--   Expected: Just Q ι r (R (R (Q ι r S)))
--   Actual:   Just Q ι r (R (R (Q ι r S)))
-- PASS: Multiple delayed substitutions
--   Permutations tested: 6
--   Failures: 0
-- PASS: Nested pop constructors
--   Permutations tested: 2
--   Failures: 0
-- PASS: Pop through multiple intervening constructors
--   Permutations tested: 2
--   Failures: 0
-- PASS: Preserve parameters of intervening constructors
--   Permutations tested: 1
--   Failures: 0
-- PASS: Two pops of the same state
--   Permutations tested: 6
--   Failures: 0
-- PASS: Conflicting pops of the same state
--   Permutations tested: 6
--   Failures: 0
-- PASS: Pop inside an arrow type
--   Permutations tested: 2
--   Failures: 0
-- PASS: Pop inside a graded type
--   Permutations tested: 2
--   Failures: 0
-- PASS: Pop cancellation before occurs check
--   Permutations tested: 1
--   Failures: 0
-- PASS: Abstract over state, retrieve QUD
--   Term:     (λx.π₁(pop_QUD(x)))(push_QUD(qReal)(state))
--   Expected: Just r → ι → t
--   Actual:   Just r → ι → t
-- PASS: Abstract over state, retrieve remainder
--   Term:     (λx.π₂(pop_QUD(x)))(push_QUD(qReal)(state))
--   Expected: Just S
--   Actual:   Just S
-- PASS: Higher-order application of pop function
--   Term:     (λf.f(push_QUD(qReal)(state)))(λx.pop_QUD(x))
--   Expected: Just ((r → ι → t) × S)
--   Actual:   Just ((r → ι → t) × S)
-- PASS: Abstract over pushed QUD
--   Term:     λx.pop_QUD(push_QUD(x)(state))
--   Expected: Just (a → i → t) → ((a → i → t) × S)
--   Actual:   Just (β → γ → t) → ((β → γ → t) × S)
-- PASS: Two uses of the same state
--   Term:     (λx.⟨π₁(pop_QUD(x)), π₁(pop_QUD(x))⟩)(push_QUD(qReal)(state))
--   Expected: Just ((r → ι → t) × (r → ι → t))
--   Actual:   Just ((r → ι → t) × (r → ι → t))
-- PASS: Incompatible uses of the same state
--   Term:     (λx.⟨π₁(pop_QUD(x))(real), π₁(pop_QUD(x))(entity)⟩)(push_QUD(qReal)(state))
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Push and pop through two abstractions
--   Term:     (λf.λx.pop_QUD(push_QUD(f)(x)))(qReal)(state)
--   Expected: Just ((r → ι → t) × S)
--   Actual:   Just ((r → ι → t) × S)
-- PASS: Pop through R with unknown tail
--   Term:     λx.pop_QUD(push_R(entity)(x))
--   Expected: Just s → ((a → i → t) × R (popQ i a s))
--   Actual:   Just (popQ η ζ α ~ popQ η ζ α) ⟹ α → ((ζ → η → t) × R (popQ η ζ α))
-- PASS: Pop Q from empty state
--   Term:     pop_QUD(state)
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Pop Q from state containing only R
--   Term:     pop_QUD(push_R(entity)(state))
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Pop Q twice from singleton Q stack
--   Term:     pop_QUD(π₂(pop_QUD(push_QUD(qReal)(state))))
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Project value from empty pop
--   Term:     π₁(pop_QUD(state))
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Incompatible pops of unknown shared state
--   Term:     λx.⟨π₁(pop_QUD(x))(real), π₁(pop_QUD(x))(entity)⟩
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Immediate push/pop reduction
--   Input:    pop_QUD(push_QUD(qReal)(state)) : ((r → ι → t) × S)
--   Expected: ⟨qReal, state⟩ : ((r → ι → t) × S)
--   Actual:   Right ⟨qReal, state⟩ : ((r → ι → t) × S)
-- PASS: Reduction through R
--   Input:    pop_QUD(push_R(entity)(push_QUD(qReal)(state))) : ((r → ι → t) × R S)
--   Expected: ⟨qReal, push_R(entity)(state)⟩ : ((r → ι → t) × R S)
--   Actual:   Right ⟨qReal, push_R(entity)(state)⟩ : ((r → ι → t) × R S)
-- PASS: Reduction through Q
--   Input:    pop_R(push_QUD(qReal)(push_R(entity)(state))) : e × Q ι r S
--   Expected: ⟨entity, push_QUD(qReal)(state)⟩ : e × Q ι r S
--   Actual:   Right ⟨entity, push_QUD(qReal)(state)⟩ : e × Q ι r S
-- PASS: Reduction of interleaved stacks
--   Input:    pop_QUD(push_R(entity)(push_QUD(qEntity)(push_R(entity)(push_QUD(qReal)(state))))) : ((e → ι → t) × R (R (Q ι r S)))
--   Expected: ⟨qEntity, push_R(entity)(push_R(entity)(push_QUD(qReal)(state)))⟩ : ((e → ι → t) × R (R (Q ι r S)))
--   Actual:   Right ⟨qEntity, push_R(entity)(push_R(entity)(push_QUD(qReal)(state)))⟩ : ((e → ι → t) × R (R (Q ι r S)))
-- PASS: Successive reductions
--   Input:    pop_R(π₂(pop_QUD(push_R(entity)(push_QUD(qEntity)(push_R(entity)(push_QUD(qReal)(state))))))) : e × R (Q ι r S)
--   Expected: ⟨entity, push_R(entity)(push_QUD(qReal)(state))⟩ : e × R (Q ι r S)
--   Actual:   Right ⟨entity, push_R(entity)(push_QUD(qReal)(state))⟩ : e × R (Q ι r S)
-- PASS: Beta reduction exposes pop redex
--   Input:    (λx.pop_QUD(x))(push_QUD(qReal)(state)) : ((r → ι → t) × S)
--   Expected: ⟨qReal, state⟩ : ((r → ι → t) × S)
--   Actual:   Right ⟨qReal, state⟩ : ((r → ι → t) × S)
-- PASS: Push/pop reduction with free state
--   Input:    pop_QUD(push_QUD(qReal)(s)) : ((r → ι → t) × α)
--   Expected: ⟨qReal, s⟩ : ((r → ι → t) × α)
--   Actual:   Right ⟨qReal, s⟩ : ((r → ι → t) × α)
-- PASS: Push/pop reduction under lambda
--   Input:    λx.pop_QUD(push_QUD(qReal)(x)) : α → ((r → ι → t) × α)
--   Expected: λx.⟨qReal, x⟩ : α → ((r → ι → t) × α)
--   Actual:   Right λx.⟨qReal, x⟩ : α → ((r → ι → t) × α)
-- PASS: Pop through R with free state
--   Input:    pop_QUD(push_R(entity)(s)) : (popQ η ζ α ~ popQ η ζ α) ⟹ ((ζ → η → t) × R (popQ η ζ α))
--   Expected: ⟨π₁(pop_QUD(s)), push_R(entity)(π₂(pop_QUD(s)))⟩ : (popQ κ ι θ ~ popQ κ ι θ) ⟹ ((ι → κ → t) × R (popQ κ ι θ))
--   Actual:   Right ⟨π₁(pop_QUD(s)), push_R(entity)(π₂(pop_QUD(s)))⟩ : (popQ κ ι θ ~ popQ κ ι θ) ⟹ ((ι → κ → t) × R (popQ κ ι θ))
-- PASS: Pop through R under lambda
--   Input:    λx.pop_QUD(push_R(entity)(x)) : (popQ η ζ α ~ popQ η ζ α) ⟹ α → ((ζ → η → t) × R (popQ η ζ α))
--   Expected: λx.⟨π₁(pop_QUD(x)), push_R(entity)(π₂(pop_QUD(x)))⟩ : (popQ κ ι θ ~ popQ κ ι θ) ⟹ θ → ((ι → κ → t) × R (popQ κ ι θ))
--   Actual:   Right λx.⟨π₁(pop_QUD(x)), push_R(entity)(π₂(pop_QUD(x)))⟩ : (popQ κ ι θ ~ popQ κ ι θ) ⟹ θ → ((ι → κ → t) × R (popQ κ ι θ))
-- >>> runDeepPopTests
-- Apparent cycle, order 1:
-- Just [(z,Q ι r s)]
-- Apparent cycle, order 2:
-- Just [(z,Q ι r s)]
-- Genuine recursive type:
-- Nothing
-- Genuine recursive type involving pop:
-- Nothing
-- Identical valid pop types:
-- Just []
-- Identical incompatible pop types:
-- Nothing
-- Identical underflowing pop types:
-- Nothing
-- Identical unresolved pop types:
-- Just [(popQ ι r s,popQ ι r s)]
-- Initially unresolved, subsequently underflowing:
-- Nothing
-- PASS: Same QUD through different access paths
--   Term:     λx.⟨π₁(pop_QUD(x)), π₁(pop_QUD(push_R(entity)(x)))⟩
--   Expected: Just s → ((a → i → t) × (a → i → t))
--   Actual:   Just (popQ ν μ β ~ popQ ν μ β) ⟹ β → ((μ → ν → t) × (μ → ν → t))
-- PASS: Conflicting requirements through R
--   Term:     λx.⟨π₁(pop_QUD(x))(real), π₁(pop_QUD(push_R(entity)(x)))(entity)⟩
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Conflicting requirements through two Rs
--   Term:     λx.⟨π₁(pop_QUD(x))(real), π₁(pop_QUD(push_R(entity)(push_R(entity)(x))))(entity)⟩
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Independent QUDs in different states
--   Term:     λx.λy.⟨π₁(pop_QUD(x))(real), π₁(pop_QUD(y))(entity)⟩
--   Expected: Just s → s' → ((i → t) × (i' → t))
--   Actual:   Just (popQ ε r γ ~ popQ ε r γ, popQ μ e κ ~ popQ μ e κ) ⟹ γ → κ → ((ε → t) × (μ → t))
-- PASS: Different QUDs in the same stack
--   Term:     λx.⟨π₁(pop_QUD(push_QUD(qReal)(x))), π₁(pop_QUD(push_QUD(qEntity)(x)))⟩
--   Expected: Just s → ((r → ι → t) × (e → ι → t))
--   Actual:   Just α → ((r → ι → t) × (e → ι → t))
-- Ordinary abstraction:
-- (λx.needsS(π₂(pop_QUD(x))))(push_QUD(qReal)(state)) : e
-- Abstraction with Return:
-- (λx.[needsS(π₂(pop_QUD(x)))])(push_QUD(qReal)(state)) : P e
-- Abstraction with probabilistic Let:
-- (λx.(z ∼ [⋄]; [needsS(π₂(pop_QUD(x)))]))(push_QUD(qReal)(state)) : P e
-- Pop on a sampled state:
-- (x ∼ [push_QUD(qReal)(state)]; [π₁(pop_QUD(x))]) : P (r → ι → t)
-- Pop on an empty sampled state:
-- ⌜(x ∼ [state]; [π₁(pop_QUD(x))])⌝ is not assigned a type.
-- Successive probabilistic bindings:
-- (x ∼ [push_QUD(qReal)(state)]; (y ∼ [pop_QUD(x)]; [π₁(y)])) : P (r → ι → t)
-- Inferred getter type:
-- Just (popQ δ γ β ~ popQ δ γ β) ⟹ β → γ → δ → t
-- Direct application to valid state:
-- (λx.π₁(pop_QUD(x)))(push_QUD(qReal)(state)) : r → ι → t
-- Constant application to valid state:
-- getter(push_QUD(qReal)(state)) : r → ι → t
-- Direct application to empty state:
-- ⌜(λx.π₁(pop_QUD(x)))(state)⌝ is not assigned a type.
-- Constant application to empty state:
-- ⌜getter(state)⌝ is not assigned a type.
-- Direct application to wrong QUD:
-- ⌜(λx.π₁(pop_QUD(x)))(push_QUD(qEntity)(state))(real)⌝ is not assigned a type.
-- Constant application to wrong QUD:
-- ⌜getter(push_QUD(qEntity)(state))(real)⌝ is not assigned a type.
-- >>> runGradeTests
-- λm.(x ∼ m; [x]) : G γ ε → G γ ε
-- λm.λk.(x ∼ m; k(x)) : G ε γ → (γ → G ζ η) → G (+ ε ζ) η
-- λm.λn.(x ∼ m; n) : G δ γ → G ε ζ → G (+ δ ε) ζ
-- >>> runGradeUnifyTests
-- Just [(+ g h,M)]
-- Just [(h,M),(g,P)]
-- Just [(g,M)]
-- Nothing
-- Just [(g,P),(h,M)]
-- Just [(g,M),(h,P)]
-- Just [(g,M),(h,M)]
-- >>> runGradeConstraintTests
-- Inferred abstraction type:
-- λm.λn.needsM((x ∼ m; n)) : (+ δ ε ~ M) ⟹ G δ γ → G ε ⋄ → e
-- P + P:
-- ⌜(λm.λn.needsM((x ∼ m; n)))([⋄])([⋄])⌝ is not assigned a type.
-- P + M:
-- (λm.λn.needsM((x ∼ m; n)))([⋄])(measure) : e
-- M + P:
-- (λm.λn.needsM((x ∼ m; n)))(measure)([⋄]) : e
-- M + M:
-- (λm.λn.needsM((x ∼ m; n)))(measure)(measure) : e
-- >>> runAllNewQualifiedTests
-- PASS: Monomorphic constant
--   Term:     qc_measure
--   Expected: Just M ⋄
--   Actual:   Just M ⋄
-- PASS: Polymorphic constant
--   Term:     qc_identity
--   Expected: Just a → a
--   Actual:   Just α → α
-- PASS: Independent polymorphic constant occurrences
--   Term:     ⟨qc_identity(real), qc_identity(entity)⟩
--   Expected: Just r × e
--   Actual:   Just r × e
-- Qualified constant in isolation:
-- qc_sumM : (+ γ ε ~ M) ⟹ G γ δ → G ε ⋄ → e
-- PASS: Qualified constant: P + P
--   Term:     qc_sumM([⋄])([⋄])
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Qualified constant: P + M
--   Term:     qc_sumM([⋄])(qc_measure)
--   Expected: Just e
--   Actual:   Just e
-- PASS: Qualified constant: M + P
--   Term:     qc_sumM(qc_measure)([⋄])
--   Expected: Just e
--   Actual:   Just e
-- PASS: Qualified constant: M + M
--   Term:     qc_sumM(qc_measure)(qc_measure)
--   Expected: Just e
--   Actual:   Just e
-- PASS: Partial constant application to P
--   Term:     qc_sumM([⋄])
--   Expected: Just M ⋄ → e
--   Actual:   Just M ⋄ → e
-- PASS: Partial constant application to M
--   Term:     qc_sumM(qc_measure)
--   Expected: Just G h ⋄ → e
--   Actual:   Just G ε ⋄ → e
-- PASS: Independent qualified constant occurrences
--   Term:     ⟨qc_sumM([⋄])(qc_measure), qc_sumM(qc_measure)([⋄])⟩
--   Expected: Just e × e
--   Actual:   Just e × e
-- PASS: One invalid qualified constant occurrence
--   Term:     ⟨qc_sumM([⋄])(qc_measure), qc_sumM([⋄])([⋄])⟩
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Hidden variable permits P
--   Term:     qc_hiddenOr([⋄])
--   Expected: Just e
--   Actual:   Just e
-- PASS: Hidden variable permits M
--   Term:     qc_hiddenOr(qc_measure)
--   Expected: Just e
--   Actual:   Just e
-- PASS: Restricted hidden variable excludes P
--   Term:     qc_hiddenRestricted([⋄])
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Restricted hidden variable permits M
--   Term:     qc_hiddenRestricted(qc_measure)
--   Expected: Just e
--   Actual:   Just e
-- PASS: Independent qualification-only variables
--   Term:     ⟨qc_hiddenP, qc_hiddenM⟩
--   Expected: Just e × e
--   Actual:   Just e × e
-- PASS: Independent hidden variables across applications
--   Term:     ⟨qc_hiddenOr([⋄]), qc_hiddenP⟩
--   Expected: Just e × e
--   Actual:   Just e × e
-- PASS: Unsatisfiable constant qualification
--   Term:     qc_impossible
--   Expected: Nothing
--   Actual:   Nothing
-- Inferred qualified signature:
-- Just (+ δ ε ~ M) ⟹ G δ γ → G ε ⋄ → e
-- PASS: Inferred constant: P + P
--   Term:     qc_inferred([⋄])([⋄])
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Inferred constant: P + M
--   Term:     qc_inferred([⋄])(qc_measure)
--   Expected: Just e
--   Actual:   Just e
-- PASS: Inferred constant: M + P
--   Term:     qc_inferred(qc_measure)([⋄])
--   Expected: Just e
--   Actual:   Just e
-- PASS: Inferred constant: M + M
--   Term:     qc_inferred(qc_measure)(qc_measure)
--   Expected: Just e
--   Actual:   Just e
-- PASS: Inferred constant: partial application to P
--   Term:     qc_inferred([⋄])
--   Expected: Just M ⋄ → e
--   Actual:   Just M ⋄ → e
-- PASS: Inferred constant: partial application to M
--   Term:     qc_inferred(qc_measure)
--   Expected: Just G h ⋄ → e
--   Actual:   Just G θ ⋄ → e
-- PASS: Independent inferred constant occurrences
--   Term:     ⟨qc_inferred([⋄])(qc_measure), qc_inferred(qc_measure)([⋄])⟩
--   Expected: Just e × e
--   Actual:   Just e × e
-- PASS: Weakening qualification
--   Input:    qc_sumM : (+ γ ε ~ M) ⟹ G γ δ → G ε ⋄ → e
--   Reduct:   qc_unrestricted : G α β → G γ ⋄ → e
--   Actual:   Right qc_unrestricted : G α β → G γ ⋄ → e
-- PASS: Strengthening qualification
--   Input:    qc_unrestricted : G α β → G γ ⋄ → e
--   Reduct:   qc_sumM : (+ γ ε ~ M) ⟹ G γ δ → G ε ⋄ → e
--   Actual:   Left "Evaluation error: qc_unrestricted : G \945 \946 \8594 G \947 \8900 \8594 e,\nwhile qc_sumM : (+ \947 \949 ~ M) \10233 G \947 \948 \8594 G \949 \8900 \8594 e"
-- PASS: First grade M entails sum M
--   Input:    qc_firstM : M γ → G δ ⋄ → e
--   Reduct:   qc_sumM : (+ γ ε ~ M) ⟹ G γ δ → G ε ⋄ → e
--   Actual:   Right qc_sumM : (+ γ ε ~ M) ⟹ G γ δ → G ε ⋄ → e
-- PASS: Sum M does not entail first grade M
--   Input:    qc_sumM : (+ γ ε ~ M) ⟹ G γ δ → G ε ⋄ → e
--   Reduct:   qc_firstM : M γ → G δ ⋄ → e
--   Actual:   Left "Evaluation error: qc_sumM : (+ \947 \949 ~ M) \10233 G \947 \948 \8594 G \949 \8900 \8594 e,\nwhile qc_firstM : M \947 \8594 G \948 \8900 \8594 e"
-- PASS: Commutativity of qualification
--   Input:    qc_sumM : (+ γ ε ~ M) ⟹ G γ δ → G ε ⋄ → e
--   Reduct:   qc_sumMReversed : (+ ε γ ~ M) ⟹ G γ δ → G ε ⋄ → e
--   Actual:   Right qc_sumMReversed : (+ ε γ ~ M) ⟹ G γ δ → G ε ⋄ → e
-- PASS: Commutativity, reverse direction
--   Input:    qc_sumMReversed : (+ ε γ ~ M) ⟹ G γ δ → G ε ⋄ → e
--   Reduct:   qc_sumM : (+ γ ε ~ M) ⟹ G γ δ → G ε ⋄ → e
--   Actual:   Right qc_sumM : (+ γ ε ~ M) ⟹ G γ δ → G ε ⋄ → e
-- PASS: Hidden variable imposes no restriction
--   Input:    qc_hiddenOr : (+ γ β ~ M) ⟹ G γ ⋄ → e
--   Reduct:   qc_hiddenFree : G α ⋄ → e
--   Actual:   Right qc_hiddenFree : G α ⋄ → e
-- PASS: Unrestricted entails existentially satisfiable constraint
--   Input:    qc_hiddenFree : G α ⋄ → e
--   Reduct:   qc_hiddenOr : (+ γ β ~ M) ⟹ G γ ⋄ → e
--   Actual:   Right qc_hiddenOr : (+ γ β ~ M) ⟹ G γ ⋄ → e
-- PASS: Restricted hidden variable weakens
--   Input:    qc_hiddenRestricted : M ⋄ → e
--   Reduct:   qc_hiddenFree : G α ⋄ → e
--   Actual:   Right qc_hiddenFree : G α ⋄ → e
-- PASS: Restricted hidden variable strengthens
--   Input:    qc_hiddenFree : G α ⋄ → e
--   Reduct:   qc_hiddenRestricted : M ⋄ → e
--   Actual:   Left "Evaluation error: qc_hiddenFree : G \945 \8900 \8594 e,\nwhile qc_hiddenRestricted : M \8900 \8594 e"
-- Qualified getter constant:
-- qc_getter : (popQ ι θ η ~ popQ ι θ η) ⟹ η → θ → ι → t
-- PASS: Qualified constant retrieves real QUD
--   Term:     qc_getter(push_QUD(qReal)(state))
--   Expected: Just r → ι → t
--   Actual:   Just r → ι → t
-- PASS: Qualified constant retrieves entity QUD
--   Term:     qc_getter(push_QUD(qEntity)(state))
--   Expected: Just e → ι → t
--   Actual:   Just e → ι → t
-- PASS: Qualified constant retrieves QUD through R
--   Term:     qc_getter(push_R(entity)(push_QUD(qReal)(state)))
--   Expected: Just r → ι → t
--   Actual:   Just r → ι → t
-- PASS: Qualified constant rejects empty state
--   Term:     qc_getter(state)
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Qualified constant rejects incompatible argument
--   Term:     qc_getter(push_QUD(qEntity)(state))(real)
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Independent qualified getter occurrences
--   Term:     ⟨qc_getter(push_QUD(qReal)(state)), qc_getter(push_QUD(qEntity)(state))⟩
--   Expected: Just ((r → ι → t) × (e → ι → t))
--   Actual:   Just ((r → ι → t) × (e → ι → t))
-- PASS: Conflicting getters of unknown state
--   Term:     λx.⟨qc_getter(x)(real), qc_getter(x)(entity)⟩
--   Expected: Nothing
--   Actual:   Nothing
-- Inferred getter qualification:
-- Just (popQ δ γ β ~ popQ δ γ β) ⟹ β → γ → δ → t
-- PASS: Inferred getter retrieves real QUD
--   Term:     qc_inferredGetter(push_QUD(qReal)(state))
--   Expected: Just r → ι → t
--   Actual:   Just r → ι → t
-- PASS: Inferred getter retrieves entity QUD
--   Term:     qc_inferredGetter(push_QUD(qEntity)(state))
--   Expected: Just e → ι → t
--   Actual:   Just e → ι → t
-- PASS: Inferred getter rejects empty state
--   Term:     qc_inferredGetter(state)
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Inferred getter rejects incompatible argument
--   Term:     qc_inferredGetter(push_QUD(qEntity)(state))(real)
--   Expected: Nothing
--   Actual:   Nothing
-- PASS: Independent inferred getter occurrences
--   Term:     ⟨qc_inferredGetter(push_QUD(qReal)(state)), qc_inferredGetter(push_QUD(qEntity)(state))⟩
--   Expected: Just ((r → ι → t) × (e → ι → t))
--   Actual:   Just ((r → ι → t) × (e → ι → t))
-- PASS: Weakening stack qualification
--   Input:    qc_getter : (popQ ι θ η ~ popQ ι θ η) ⟹ η → θ → ι → t
--   Reduct:   qc_unrestrictedGetter : α → β → γ → t
--   Actual:   Right qc_unrestrictedGetter : α → β → γ → t
-- PASS: Strengthening stack qualification
--   Input:    qc_unrestrictedGetter : α → β → γ → t
--   Reduct:   qc_getter : (popQ ι θ η ~ popQ ι θ η) ⟹ η → θ → ι → t
--   Actual:   Left "Evaluation error: qc_unrestrictedGetter : \945 \8594 \946 \8594 \947 \8594 t,\nwhile qc_getter : (popQ \953 \952 \951 ~ popQ \953 \952 \951) \10233 \951 \8594 \952 \8594 \953 \8594 t"
