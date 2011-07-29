module Language.ImProve.Path
  ( totalPaths
  ) where

import Language.ImProve.Core

totalPaths :: Name -> Statement -> IO ()
totalPaths name stmt = do
  putStrLn $ "total paths: " ++ show (paths stmt)
  writeFile (name ++ ".dot") (dot stmt)

paths :: Statement -> Integer
paths a = case a of
  Assign _ _      -> 1
  Branch _ a b    -> paths a + paths b
  Sequence a b    -> paths a * paths b
  Assert _ _ _ -> 1
  Assume  _ _     -> 1
  Label  _ a      -> paths a
  Null            -> 1

dot :: Statement -> String
dot stmt = unlines $ ["digraph {"] ++ links ++ ["}"]
  where
  (_, _, links) = d 0 1 stmt

d :: Int -> Int -> Statement -> (Int, Int, [String])
d src id a = case a of
  Branch _ a b -> (id2, id2 + 1, link src id ++ a' ++ b' ++ link srcA id2 ++ link srcB id2)
    where
    (srcA, id1, a') = d id (id + 1)  a
    (srcB, id2, b') = d id  id1      b
  Sequence a b -> (srcB, id2, a' ++ b')
    where
    (srcA, id1, a') = d src id  a
    (srcB, id2, b') = d srcA id1 b
  Label  _ a -> d src id a
  _ -> (src, id, [])
  where
  link :: Int -> Int -> [String]
  link a b = ["  " ++ show a ++ " -> " ++ show b]

