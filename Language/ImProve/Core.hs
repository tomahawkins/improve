module Language.ImProve.Core
  ( E (..)
  , V (..)
  , UV (..)
  , Name
  , Path
  , UID
  , PathName (..)
  , AllE (..)
  , NumE
  , Const (..)
  , Statement (..)
  , VarInfo
  , varInfo
  , stmtVars
  , exprVars
  , theorems
  ) where

import Data.List
import Data.Ratio

type Name = String

type Path = [Name]

type UID = Int

-- | A mutable variable.
data V a = V Bool [Name] a deriving (Eq, Ord)

-- | An untyped variable.
data UV
  = UVBool  (V Bool)
  | UVInt   (V Int)
  | UVFloat (V Float)
  deriving (Eq, Ord)

class    PathName a         where pathName :: a -> String
instance PathName Path      where pathName = intercalate "."
instance PathName (V a)     where pathName (V _ path _) = pathName path
instance PathName VarInfo   where pathName (_, path, _) = pathName path

class Eq a => AllE a where
  zero   :: (Name -> a -> m (V a)) -> a
  const' :: a -> Const
  untype :: V a -> UV

instance AllE Bool where
  zero = const False
  const' = Bool
  untype = UVBool

instance AllE Int where
  zero = const 0
  const' = Int
  untype = UVInt
  
instance AllE Float where
  zero = const 0
  const' = Float
  untype = UVFloat

class    AllE a => NumE a
instance NumE Int
instance NumE Float

-- | A logical, arithmetic, comparative, or conditional expression.
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

data Statement where
  Assign   :: AllE a => V a -> E a -> Statement
  Branch   :: E Bool -> Statement -> Statement -> Statement
  Sequence :: Statement -> Statement -> Statement
  Theorem  :: Int -> Int -> [Int] -> E Bool -> Statement -- Theorem id k lemmas expr
  Assume   :: E Bool -> Statement
  Label    :: Name -> Statement -> Statement
  Null     :: Statement

data Const
  = Bool  Bool
  | Int   Int
  | Float Float
  deriving (Show, Eq, Ord)

type VarInfo = (Bool, Path, Const)

class VarInfo' a where varInfo :: a -> VarInfo
instance AllE a => VarInfo' (V a) where varInfo (V input path init) = (input, path, const' init)
instance VarInfo' UV where
  varInfo a = case a of
    UVBool a  -> varInfo a
    UVInt  a  -> varInfo a
    UVFloat a -> varInfo a

-- | Variables in a program.
stmtVars :: Statement -> [UV]
stmtVars a = case a of
  Assign a b   -> nub $ untype a : exprVars b
  Branch a b c -> nub $ exprVars a ++ stmtVars b ++ stmtVars c
  Sequence a b -> nub $ stmtVars a ++ stmtVars b
  Theorem _ _ _ a -> exprVars a
  Assume a     -> exprVars a
  Label  _ a   -> stmtVars a
  Null         -> []

-- | Variables in an expression.
exprVars :: E a -> [UV]
exprVars a = case a of
  Ref a     -> [untype a]
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

-- | Theorems in a program.
theorems :: Statement -> [(Int, Int, [Int], E Bool)]
theorems a = case a of
  Theorem id k lemmas expr -> [(id, k, lemmas, expr)]
  Assign _ _   -> []
  Branch _ a b -> theorems a ++ theorems b
  Sequence a b -> theorems a ++ theorems b
  Assume _     -> []
  Label  _ a   -> theorems a
  Null         -> []

