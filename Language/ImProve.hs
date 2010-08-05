module Language.ImProve
  (
  -- * Types
    E
  , V
  , AllE
  , NumE
  , Name
  -- * Expressions
  -- ** Constants
  , true
  , false
  -- ** Variable Reference
  , ref
  -- ** Logical Operations
  , not_
  , (&&.)
  , (||.)
  , and_
  , or_
  , any_
  , all_
  , imply
  -- ** Equality and Comparison
  , (==.)
  , (/=.)
  , (<.)
  , (<=.)
  , (>.)
  , (>=.)
  -- ** Min, max, and limiting.
  , min_
  , minimum_
  , max_
  , maximum_
  , limit
  -- ** Arithmetic Operations
  , div_
  , mod_
  -- ** Conditional Operator
  , mux
  -- * Hierarchical Scope
  , scope
  -- * Variable Declarations
  , bool
  , int
  , float
  -- * Statements
  , Stmt
  -- ** Variable Assignment
  , (<==)
  -- ** Conditional Branching
  , branch
  -- ** Incrementing and decrementing.
  , incr
  , decr
  -- ** Assertions and  Assumptions
  , assert
  , assume
  -- * Compilation
  , compile
  ) where

import Control.Monad
import Data.Ratio

infix  4 ==., /=., <., <=., >., >=.
infixl 3 &&.
infixl 2 ||.
infixr 1 <==

type Name = String

-- | Variables.
data V a = V [Name] a deriving Eq

-- | All types.
class    AllE a
instance AllE Bool
instance AllE Int
instance AllE Float

-- | Number types.
class    NumE a
instance NumE Int
instance NumE Float

-- | Core expressions.
data E a where
  Ref   :: V a -> E a
  Const :: a -> E a
  Add   :: NumE a => E a -> E a -> E a
  Sub   :: NumE a => E a -> E a -> E a
  Mul   :: NumE a => E a -> E a -> E a
  Div   :: NumE a => E a -> E a -> E a
  Mod   :: E Int -> E Int -> E Int
  Not   :: E Bool -> E Bool
  And   :: E Bool -> E Bool -> E Bool
  Or    :: E Bool -> E Bool -> E Bool
  Eq    :: AllE a => E a -> E a -> E Bool
  Lt    :: NumE a => E a -> E a -> E Bool
  Mux   :: E Bool -> E a -> E a -> E a

instance Show (E a) where show = undefined 
instance Eq   (E a) where (==) = undefined

instance (Num a, AllE a, NumE a) => Num (E a) where
  (+) = Add
  (-) = Sub
  (*) = Mul
  negate a = 0 - a
  abs a = mux (a <. 0) (negate a) a
  signum a = mux (a ==. 0) 0 $ mux (a <. 0) (-1) 1
  fromInteger = Const . fromInteger

instance Fractional (E Float) where
  (/) = Div
  recip a = 1 / a
  fromRational r = Const $ fromInteger (numerator r) / fromInteger (denominator r)

-- | True term.
true :: E Bool
true = Const True

-- | False term.
false :: E Bool
false = Const False

-- | Logical negation.
not_ :: E Bool -> E Bool
not_ = Not

-- | Logical AND.
(&&.) :: E Bool -> E Bool -> E Bool
(&&.) = And

-- | Logical OR.
(||.) :: E Bool -> E Bool -> E Bool
(||.) = Or

-- | The conjunction of a E Bool list.
and_ :: [E Bool] -> E Bool
and_ = foldl (&&.) true

-- | The disjunction of a E Bool list.
or_ :: [E Bool] -> E Bool
or_ = foldl (||.) false

-- | True iff the predicate is true for all elements.
all_ :: (a -> E Bool) -> [a] -> E Bool
all_ f a = and_ $ map f a

-- | True iff the predicate is true for any element.
any_ :: (a -> E Bool) -> [a] -> E Bool
any_ f a = or_ $ map f a

-- Logical implication (if a then b).
imply :: E Bool -> E Bool -> E Bool 
imply a b = not_ a ||. b

-- | Equal.
(==.) :: AllE a => E a -> E a -> E Bool
(==.) = Eq

-- | Not equal.
(/=.) :: AllE a => E a -> E a -> E Bool
a /=. b = not_ (a ==. b)

-- | Less than.
(<.) :: NumE a => E a -> E a -> E Bool
(<.) = Lt

-- | Greater than.
(>.) :: NumE a => E a -> E a -> E Bool
a >. b = b <. a

-- | Less than or equal.
(<=.) :: NumE a => E a -> E a -> E Bool
a <=. b =  not_ (a >. b)

-- | Greater than or equal.
(>=.) :: NumE a => E a -> E a -> E Bool
a >=. b = not_ (a <. b)

-- | Returns the minimum of two numbers.
min_ :: NumE a => E a -> E a -> E a
min_ a b = mux (a <=. b) a b

-- | Returns the minimum of a list of numbers.
minimum_ :: NumE a => [E a] -> E a
minimum_ = foldl1 min_

-- | Returns the maximum of two numbers.
max_ :: NumE a => E a -> E a -> E a
max_ a b = mux (a >=. b) a b

-- | Returns the maximum of a list of numbers.
maximum_ :: NumE a => [E a] -> E a
maximum_ = foldl1 max_

-- | Limits between min and max.
limit :: NumE a => E a -> E a -> E a -> E a
limit a b i = max_ min $ min_ max i
  where
  min = min_ a b
  max = max_ a b

-- | Integral division.
div_ :: E Int -> E Int -> E Int
div_ = Div

-- | Modulo.
mod_ :: E Int -> E Int -> E Int
mod_ = Mod

-- | References a variable.
ref :: V a -> E a
ref = Ref

-- | Conditional expression.  Note, both branches are evaluated!
--
-- > mux test onTrue onFalse
mux :: E Bool -> E a -> E a -> E a
mux = Mux

-- | Creates a hierarchical scope.
scope :: Name -> Stmt a -> Stmt a
scope name (Stmt f0) = Stmt f1
  where
  f1 (scope, statement) = (a, (scope, statement1))
    where
    (a, (_, statement1)) = f0 (scope ++ [name], statement)
  
getScope :: Stmt [Name]
getScope = Stmt $ \ (scope, statement) -> (scope, (scope, statement))

var :: AllE a => Name -> a -> Stmt (V a)
var name init = do
  scope <- getScope
  return $ V (scope ++ [name]) init

-- | Boolean variable declaration.
bool :: Name -> Bool -> Stmt (V Bool)
bool = var

-- | Int variable declaration.
int :: Name -> Int -> Stmt (V Int)
int = var

-- | Float variable declaration.
float :: Name -> Float -> Stmt (V Float)
float = var

-- | Increments an E Int.
incr :: V Int -> Stmt ()
incr a = a <== ref a + 1

-- | Decrements an E Int.
decr :: V Int -> Stmt ()
decr a = a <== ref a - 1

data Statement
  = AssignBool  (V Bool ) (E Bool )
  | AssignInt   (V Int  ) (E Int  )
  | AssignFloat (V Float) (E Float)
  | Branch (E Bool) Statement Statement
  | Sequence Statement Statement
  | Assert [Name] (E Bool)
  | Assume [Name] (E Bool)
  | Null

-- | The Stmt monad holds variable declarations and statements.
data Stmt a = Stmt (([Name], Statement) -> (a, ([Name], Statement)))

instance Monad Stmt where
  return a = Stmt $ \ s -> (a, s)
  (Stmt f1) >>= f2 = Stmt f3
    where
    f3 s1 = f4 s2
      where
      (a, s2) = f1 s1
      Stmt f4 = f2 a

statement :: Statement -> Stmt ()
statement a = Stmt $ \ (scope, statement) -> ((), (scope, Sequence statement a))

evalStmt :: [Name] -> Stmt () -> Statement
evalStmt scope (Stmt f) = snd $ snd $ f (scope, Null)

class    Assign a     where (<==) :: V a -> E a -> Stmt ()
instance Assign Bool  where a <== b = statement $ AssignBool  a b
instance Assign Int   where a <== b = statement $ AssignInt   a b
instance Assign Float where a <== b = statement $ AssignFloat a b

-- | Assert that a condition is true.
assert :: Name -> E Bool -> Stmt ()
assert a b = do
  scope <- getScope
  statement $ Assert (scope ++ [a]) b

-- | Declare an assumption condition is true.
assume :: Name -> E Bool -> Stmt ()
assume a b = do
  scope <- getScope
  statement $ Assume (scope ++ [a]) b

-- | Conditional branch.
branch :: E Bool -> Stmt () -> Stmt () -> Stmt ()
branch cond onTrue onFalse = do
  scope <- getScope
  statement $ Branch cond (evalStmt scope onTrue) (evalStmt scope onFalse)

-- | Generate C code.
compile :: Name -> Stmt () -> IO ()
compile name program = undefined

