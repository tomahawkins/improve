module Language.ImProve.Core
  ( E (..)
  , V (..)
  , Name
  , Path
  , PathName (..)
  , AllE (..)
  , NumE
  , Const (..)
  , Statement (..)
  , VarInfo
  , varInfo
  , stmtVars
  , exprVars
  ) where

import Data.List
import Data.Ratio

type Name = String

type Path = [Name]

data V a = V Bool [Name] a deriving Eq

class    PathName a         where pathName :: a -> String
instance PathName Path      where pathName = intercalate "."
instance PathName (V a)     where pathName (V _ path _) = pathName path
instance PathName VarInfo   where pathName (_, path, _) = pathName path
instance PathName Statement where
  pathName a = case a of
    Branch p _ _ _ -> pathName p
    Assert p _     -> pathName p
    Assume p _     -> pathName p
    _ -> undefined

class AllE a where
  zero   :: (Name -> a -> m (V a)) -> a
  const' :: a -> Const

instance AllE Bool where
  zero = const False
  const' = Bool

instance AllE Int where
  zero = const 0
  const' = Int
  
instance AllE Float where
  zero = const 0
  const' = Float

class    AllE a => NumE a
instance NumE Int
instance NumE Float

data E a where
  Ref   :: AllE a => V a -> E a
  Const :: AllE a => a -> E a
  Add   :: NumE a => E a -> E a -> E a
  Sub   :: NumE a => E a -> E a -> E a
  Mul   :: NumE a => E a -> a -> E a
  Div   :: NumE a => E a -> a -> E a
  Mod   :: E Int -> Int -> E Int
  Not   :: E Bool -> E Bool
  And   :: E Bool -> E Bool -> E Bool
  Or    :: E Bool -> E Bool -> E Bool
  Eq    :: AllE a => E a -> E a -> E Bool
  Lt    :: NumE a => E a -> E a -> E Bool
  Gt    :: NumE a => E a -> E a -> E Bool
  Le    :: NumE a => E a -> E a -> E Bool
  Ge    :: NumE a => E a -> E a -> E Bool
  Mux   :: AllE a => E Bool -> E a -> E a -> E a

instance Show (E a) where show = undefined 
instance Eq   (E a) where (==) = undefined

instance (Num a, AllE a, NumE a) => Num (E a) where
  (+) = Add
  (-) = Sub
  (*) = error "general multiplication not supported, use (*.)"
  negate a = 0 - a
  abs a = Mux (Lt a 0) (negate a) a
  signum a = Mux (Eq a 0) 0 $ Mux (Lt a 0) (-1) 1
  fromInteger = Const . fromInteger

instance Fractional (E Float) where
  (/) = error "general division not supported, use (/.)"
  recip a = 1 / a
  fromRational r = Const $ fromInteger (numerator r) / fromInteger (denominator r)

data Statement
  = AssignBool  (V Bool ) (E Bool )
  | AssignInt   (V Int  ) (E Int  )
  | AssignFloat (V Float) (E Float)
  | Branch      Path (E Bool) Statement Statement
  | Sequence    Statement Statement
  | Assert      Path (E Bool)
  | Assume      Path (E Bool)
  | Annotate    Name Statement
  | Null

data Const
  = Bool  Bool
  | Int   Int
  | Float Float
  deriving Eq

type VarInfo = (Bool, Path, Const)

varInfo :: AllE a => V a -> VarInfo
varInfo (V input path init) = (input, path, const' init)

-- Information about all of a program's variables.
stmtVars :: Statement -> [VarInfo]
stmtVars a = case a of
  AssignBool  a b -> nub $ varInfo a : exprVars b
  AssignInt   a b -> nub $ varInfo a : exprVars b
  AssignFloat a b -> nub $ varInfo a : exprVars b
  Branch _ a b c  -> nub $ exprVars a ++ stmtVars b ++ stmtVars c
  Sequence a b    -> nub $ stmtVars a ++ stmtVars b
  Assert _ a      -> exprVars a
  Assume _ a      -> exprVars a
  Annotate _ a    -> stmtVars a
  Null            -> []

-- Information about all of an expressions's variables.
exprVars :: E a -> [VarInfo]
exprVars a = case a of
  Ref a     -> [varInfo a]
  Const _   -> []
  Add a b   -> exprVars a ++ exprVars b
  Sub a b   -> exprVars a ++ exprVars b
  Mul a _   -> exprVars a
  Div a _   -> exprVars a
  Mod a _   -> exprVars a
  Not a     -> exprVars a
  And a b   -> exprVars a ++ exprVars b
  Or  a b   -> exprVars a ++ exprVars b
  Eq  a b   -> exprVars a ++ exprVars b
  Lt  a b   -> exprVars a ++ exprVars b
  Gt  a b   -> exprVars a ++ exprVars b
  Le  a b   -> exprVars a ++ exprVars b
  Ge  a b   -> exprVars a ++ exprVars b
  Mux a b c -> exprVars a ++ exprVars b ++ exprVars c

