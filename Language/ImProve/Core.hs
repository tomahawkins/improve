module Language.ImProve.Core
  ( E (..)
  , V (..)
  , Name
  , AllE (..)
  , NumE
  , Statement (..)
  ) where

import Data.Ratio

type Name = String

data V a
  = V   [Name] a
  | VIn [Name]

class AllE a where
  showConst :: a -> String
  showType  :: a -> String
  zero      :: (Name -> a -> m (V a)) -> a

instance AllE Bool where
  showConst a = case a of
    True  -> "1"
    False -> "0"
  showType _ = "int"
  zero = const False

instance AllE Int where
  showConst = show
  showType _ = "int"
  zero = const 0
  
instance AllE Float where
  showConst = show
  showType _ = "float"
  zero = const 0

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
  | Branch      (E Bool) Statement Statement
  | Sequence    Statement Statement
  | Assert      [Name] (E Bool)
  | Assume      [Name] (E Bool)
  | Null

