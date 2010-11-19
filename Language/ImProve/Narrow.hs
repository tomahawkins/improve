module Language.ImProve.Narrow (narrow) where

import Data.List
import Data.Maybe

import Language.ImProve.Core

narrow :: Statement -> Statement
narrow stmt = assumes
  where
  assumes = foldl Sequence Null [ Label lab $ Assume assume | (lab, opt) <- optimizations, assume <- opt stmt ]
  optimizations =
    [ ("constantAssigns", constantAssigns)
    ]

constantAssigns :: Statement -> [E Bool]
constantAssigns stmt = mapMaybe f1 $ stmtVars stmt
  where
  f1 :: VarInfo -> Maybe (E Bool)
  f1 info@(input, path, init)
    | input = Nothing
    | otherwise = do
      assigns <- lastConstAssign info stmt
      case (init, nub $ init : assigns) of
        (Bool _, [_, _]) -> Nothing
	(_, a) -> return $ foldl1 Or $ map f2 a
      where
      f2 :: Const -> E Bool
      f2 assign = case (init, assign) of
        (Bool  a, Bool  b) -> Eq (Ref (V input path a)) (Const b)
        (Int   a, Int   b) -> Eq (Ref (V input path a)) (Const b)
        (Float a, Float b) -> Eq (Ref (V input path a)) (Const b)
        _ -> undefined

lastConstAssign :: VarInfo -> Statement -> Maybe [Const]
lastConstAssign info a = do
  (_, a) <- lastConstAssign a
  return $ nub a
  where
  lastConstAssign :: Statement -> Maybe (Bool, [Const])
  lastConstAssign a = case a of
    AssignBool  v (Const a) | varInfo v == info -> Just (True, [const' a])
    AssignInt   v (Const a) | varInfo v == info -> Just (True, [const' a])
    AssignFloat v (Const a) | varInfo v == info -> Just (True, [const' a])
    AssignBool  v _ | varInfo v == info -> Nothing
    AssignInt   v _ | varInfo v == info -> Nothing
    AssignFloat v _ | varInfo v == info -> Nothing
    Branch _ a b -> do
      (aDone, a) <- lastConstAssign a
      (bDone, b) <- lastConstAssign b
      return (aDone && bDone, a ++ b)
    Sequence a b -> do
      (bDone, b) <- lastConstAssign b
      if bDone
        then return (True, b)
	else do
          (aDone, a) <- lastConstAssign a
          return (aDone, a ++ b)
    Label  _ a -> lastConstAssign a
    _ -> Just (False, [])

