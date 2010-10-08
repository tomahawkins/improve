-- | Building hierarchy from unstructured hierarchical paths.
module Language.ImProve.Tree
  ( Tree (..)
  , tree
  ) where

import Data.Function
import Data.List

data Tree a b
  = Branch a [Tree a b]
  | Leaf   a b

tree :: (Eq a, Ord a) => (b -> [a]) -> [b] -> [Tree a b]
tree path leaves = foldl mergeTrees [] [ singleTree (path leaf) leaf | leaf <- leaves ]

label :: Tree a b -> a
label (Branch a _) = a
label (Leaf   a _) = a

isBranch :: Tree a b -> Bool
isBranch (Branch _ _) = True
isBranch _ = False

singleTree :: [a] -> b -> Tree a b
singleTree [] _ = undefined
singleTree [a] b = Leaf a b
singleTree (a:b) c = Branch a [singleTree b c]

mergeTrees :: (Eq a, Ord a) => [Tree a b] -> Tree a b -> [Tree a b]
mergeTrees trees t@(Leaf _ _) = insertTree t trees
mergeTrees trees t@(Branch n branches) = case find' (\ t -> isBranch t && label t == n) trees of
    Nothing -> insertTree t trees
    Just (Branch n trees1, trees2) -> insertTree (Branch n (foldl mergeTrees trees1 branches)) trees2
    Just (Leaf _ _, _) -> undefined

insertTree :: Ord a => Tree a b -> [Tree a b] -> [Tree a b]
insertTree a b = insertBy (compare `on` label) a b

find' :: (a -> Bool) -> [a] -> Maybe (a, [a])
find' _ [] = Nothing
find' f (a:b) | f a = Just (a, b)
              | otherwise = do
  (found, rest) <- find' f b
  return (found, a : rest)

