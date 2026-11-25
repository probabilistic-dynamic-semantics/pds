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
      Just (rTy :→ iTy :→ tTy)
    constants (Left "qEntity") =
      Just (eTy :→ iTy :→ tTy)
    constants (Left "state") = Just sTy
    constants (Left "entity") = Just eTy
    constants (Left "real") = Just rTy
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
        (Just x, Just y) -> tyEq (const Nothing) x y
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
        (Right (Typed actual (Just actualTy)), Just expectedTy) ->
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
probeSig (Left "needsS") = Just (sTy :→ eTy)
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
--   Actual:   Just β → ((γ → δ → t) × popQ δ γ β)
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
--   Actual:   Just α → ((ζ → η → t) × R (popQ η ζ α))
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
--   Input:    pop_QUD(push_R(entity)(s)) : ((ζ → η → t) × R (popQ η ζ α))
--   Expected: ⟨π₁(pop_QUD(s)), push_R(entity)(π₂(pop_QUD(s)))⟩ : ((ι → κ → t) × R (popQ κ ι θ))
--   Actual:   Right ⟨π₁(pop_QUD(s)), push_R(entity)(π₂(pop_QUD(s)))⟩ : ((ι → κ → t) × R (popQ κ ι θ))
-- PASS: Pop through R under lambda
--   Input:    λx.pop_QUD(push_R(entity)(x)) : α → ((ζ → η → t) × R (popQ η ζ α))
--   Expected: λx.⟨π₁(pop_QUD(x)), push_R(entity)(π₂(pop_QUD(x)))⟩ : θ → ((ι → κ → t) × R (popQ κ ι θ))
--   Actual:   Right λx.⟨π₁(pop_QUD(x)), push_R(entity)(π₂(pop_QUD(x)))⟩ : θ → ((ι → κ → t) × R (popQ κ ι θ))
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
-- >>> runGradeTests
-- λm.(x ∼ m; [x]) : G γ ε → G γ ε
-- λm.λk.(x ∼ m; k(x)) : G ε γ → (γ → G ζ η) → G (+ ε ζ) η
-- λm.λn.(x ∼ m; n) : G δ γ → G ε ζ → G (+ δ ε) ζ
