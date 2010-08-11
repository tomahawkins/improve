-- | ImProve examples.
module Language.ImProve.Examples
  ( buildGCD
  , counter
  , verifyCounter
  , arbiterSpec
  , arbiter
  , arbiter1
  , arbiter2
  , arbiter3
  , verifyArbiters
  , buildArbiters
  , runAll
  ) where

import Language.ImProve

-- | Computes the greatest common divison of two integers.
--   Returns true if the computation is done, and the result.
gcd' :: E Int -> E Int -> Stmt (E Bool, E Int)
gcd' a b = do
  a0 <- int "a0" 0  -- Copy of input 'a'.
  b0 <- int "b0" 0  -- Copy of input 'b'.
  a1 <- int "a1" 0  -- Working copy of 'a'.
  b1 <- int "b1" 0  -- Working copy of 'b'.

  -- A new input to process.
  if_ "startNew" (a /=. ref a0 ||. b /=. ref b0) $ do
    a0 <== a
    b0 <== b
    a1 <== a
    b1 <== b

  -- Reduce a1.
  if_ "reduceA" (ref a1 >. ref b1) $ do
    a1 <== ref a1 - ref b1

  -- Reduce b1.
  if_ "reduceB" (ref b1 >. ref a1) $ do
    b1 <== ref b1 - ref a1

  -- Done if a1 == b1.
  return (ref a1 ==. ref b1, ref a1)


-- | A top level wrapper for gcd'.
gcdMain :: Stmt ()
gcdMain = do
  a <- input int "a"  -- Input variable 'a'.
  b <- input int "b"  -- Input variable 'b'.
  done   <- bool "done"   False  -- Variable signalling completion.
  result <- int  "result" 0      -- Result of GCD.

  -- Call gcd' in its own scope.  (Scopes prevent variable name collisions.)
  (done', result') <- scope "gcd" $ gcd' a b

  -- Bind the results to the output variables.
  done   <== done'
  result <== result'


-- | Build the gcdMain code (i.e. gcd.c, gcd.h).
buildGCD :: IO ()
buildGCD = code "gcd" gcdMain



-- | A rolling counter verification example.
counter :: Stmt ()
counter = do
  -- The counter variable.
  counter <- int "counter" 0

  -- Specification.
  assert "GreaterThanOrEqualTo0" $ ref counter >=. 0
  assert "LessThan10"            $ ref counter <.  10

  -- Implementation.
  ifelse "ResetCounter" (ref counter ==. 10) (counter <== 0) (counter <== ref counter + 1)

  -- Alternatives to try.
  --ifelse "ResetCounter" (ref counter >=. 9) (counter <== 0) (counter <== ref counter + 1)
  --ifelse "ResetCounter" (ref counter >=. 9 ||. ref counter <. 0)  (counter <== 0) (counter <== ref counter + 1)

-- | Verify the 'counter' example.
verifyCounter :: IO ()
verifyCounter = verify "yices" 20 counter



-- | Arbiter specification.
arbiterSpec :: (E Bool, E Bool, E Bool) -> (E Bool, E Bool, E Bool) -> Stmt ()
arbiterSpec (requestA, requestB, requestC) (grantA, grantB, grantC) = do

  -- Mutual exclusion.  At most, only one requester granted at a time.
  assert "OneHot" $      grantA &&. not_ grantB &&. not_ grantC
                ||. not_ grantA &&.      grantB &&. not_ grantC
                ||. not_ grantA &&. not_ grantB &&.      grantC
                ||. not_ grantA &&. not_ grantB &&. not_ grantC
  
  -- No grants without requests.
  assert "NotRequestedA" $ imply (not_ requestA) (not_ grantA)
  assert "NotRequestedB" $ imply (not_ requestB) (not_ grantB)
  assert "NotRequestedC" $ imply (not_ requestC) (not_ grantC)

  -- Grants to single requests.
  assert "OnlyRequestA" $ imply (     requestA &&. not_ requestB &&. not_ requestC) grantA
  assert "OnlyRequestB" $ imply (not_ requestA &&.      requestB &&. not_ requestC) grantB
  assert "OnlyRequestC" $ imply (not_ requestA &&. not_ requestB &&.      requestC) grantC

  -- Priority.
  assert "Highest" $ imply requestA grantA
  assert "Medium"  $ imply (not_ requestA &&. requestB) grantB
  assert "Lowest"  $ imply (not_ requestA &&. not_ requestB &&. requestC) grantC

-- | An arbiter implementation.
arbiter1 :: (E Bool, E Bool, E Bool) -> Stmt (E Bool, E Bool, E Bool)
arbiter1 (requestA, requestB, requestC) = do
  let grantA = requestA
      grantB = requestB
      grantC = requestC
  return (grantA, grantB, grantC)

-- | An another arbiter implementation.
arbiter2 :: (E Bool, E Bool, E Bool) -> Stmt (E Bool, E Bool, E Bool)
arbiter2 (requestA, requestB, requestC) = do
  grantA <- bool "grantA" False
  grantB <- bool "grantB" False
  grantC <- bool "grantC" False

  if_ "GrantA" (requestA)                                     (grantA <== true)
  if_ "GrantB" (not_ requestA &&. requestB)                   (grantB <== true)
  if_ "GrantC" (not_ requestA &&. not_ requestB &&. requestC) (grantC <== true)

  return (ref grantA, ref grantB, ref grantC)

-- | Yet another arbiter implementation.
arbiter3 :: (E Bool, E Bool, E Bool) -> Stmt (E Bool, E Bool, E Bool)
arbiter3 (requestA, requestB, requestC) = do
  let grantA = requestA
      grantB = not_ requestA &&. requestB
      grantC = not_ requestA &&. not_ requestB &&. requestC
  return (grantA, grantB, grantC)

-- | Binding an arbiter implemenation to the arbiter specification.
arbiter :: Name -> ((E Bool, E Bool, E Bool) -> Stmt (E Bool, E Bool, E Bool)) -> Stmt ()
arbiter name implementation = scope name $ do
  -- Create input variables.
  requestA <- input bool "requestA"
  requestB <- input bool "requestB"
  requestC <- input bool "requestC"
  let requests = (requestA, requestB, requestC)

  -- Instantiate implementation.
  grants@(grantA, grantB, grantC) <- scope "impl" $ implementation requests

  -- Bind specification.
  arbiterSpec requests grants

  -- Create output variables.
  bool' "grantA" grantA
  bool' "grantB" grantB
  bool' "grantC" grantC
  return ()

-- | Verify the different arbiter implementations.
verifyArbiters :: IO ()
verifyArbiters = do
  putStrLn "\nVerifying arbiter1 ..."
  verify "yices" 20 $ arbiter "arbiter1" arbiter1

  putStrLn "\nVerifying arbiter2 ..."
  verify "yices" 20 $ arbiter "arbiter2" arbiter2

  putStrLn "\nVerifying arbiter2 ..."
  verify "yices" 20 $ arbiter "arbiter3" arbiter3

-- | Build the different arbiter implementations.
buildArbiters :: IO ()
buildArbiters = do
  putStrLn "\nBuilding arbiter1 (arbiter1.c/h) ..."
  code "arbiter1" $ arbiter "arbiter1" arbiter1

  putStrLn "\nBuilding arbiter2 (arbiter2.c/h) ..."
  code "arbiter2" $ arbiter "arbiter2" arbiter2

  putStrLn "\nBuilding arbiter3 (arbiter3.c/h) ..."
  code "arbiter3" $ arbiter "arbiter3" arbiter3

-- | Run all examples.
runAll :: IO ()
runAll = do
  putStrLn "\nBuilding GCD (gcd.c, gcd.h) ..."
  buildGCD
  putStrLn "\nVerifying counter ..."
  verifyCounter
  putStrLn "\nVerifying arbiters ..."
  verifyArbiters
  putStrLn "\nBuilding arbiters ..."
  buildArbiters

