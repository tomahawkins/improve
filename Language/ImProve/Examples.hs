-- | ImProve examples.
module Language.ImProve.Examples
  ( gcd'
  , gcdMain
  , gcdBuild
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
gcdBuild :: IO ()
gcdBuild = code "gcd" gcdMain

