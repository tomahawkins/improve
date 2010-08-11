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
  , constant
  , zero
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
  -- ** Min, Max, and Limiting
  , min_
  , minimum_
  , max_
  , maximum_
  , limit
  -- ** Arithmetic Operations
  , (*.)
  , (/.)
  , div_
  , mod_
  -- ** Conditional Operator
  , mux
  -- ** Lookups
  , linear
  -- * Hierarchical Scope
  , scope
  -- * Statements
  , Stmt
  -- ** Variable Declarations
  , bool
  , bool'
  , int
  , int'
  , float
  , float'
  , input
  -- ** Variable Assignment
  , (<==)
  -- ** Conditional Execution
  , ifelse
  , if_
  -- ** Incrementing and decrementing.
  , incr
  , decr
  -- ** Assertions and  Assumptions
  , assert
  , assume
  -- * Verification
  , verify
  -- * Code Generation
  , code
  ) where

import Control.Monad

import Language.ImProve.Core
import qualified Language.ImProve.Verify as V
import qualified Language.ImProve.Code   as C

infixl 7 *., /., `div_`, `mod_`
infix  4 ==., /=., <., <=., >., >=.
infixl 3 &&.
infixl 2 ||.
infixr 1 <==

-- | True term.
true :: E Bool
true = Const True

-- | False term.
false :: E Bool
false = Const False

-- | Arbitrary constants.
constant :: AllE a => a -> E a
constant = Const

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
(>.) = Gt

-- | Less than or equal.
(<=.) :: NumE a => E a -> E a -> E Bool
(<=.) = Le

-- | Greater than or equal.
(>=.) :: NumE a => E a -> E a -> E Bool
(>=.) = Ge

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

-- | Multiplication.
(*.) :: NumE a => E a -> a -> E a
(*.) = Mul

-- | Floating point division.
(/.) :: E Float -> Float -> E Float
_ /. 0 = error "divide by zero (/.)"
a /. b = Div a b

-- | Integer division.
div_ :: E Int -> Int -> E Int
div_ _ 0 = error "divide by zero (div_)"
div_ a b = Div a b

-- | Modulo.
mod_ :: E Int -> Int -> E Int
mod_ _ 0 = error "divide by zero (mod_)"
mod_ a b = Mod a b

-- | Linear interpolation and extrapolation between two points.
linear :: (Float, Float) -> (Float, Float) -> E Float -> E Float
linear (x1, y1) (x2, y2) a = a *. slope + constant inter
  where
  slope = (y2 - y1) / (x2 - x1)
  inter = y1 - slope * x1

-- | References a variable.
ref :: AllE a => V a -> E a
ref = Ref

-- | Conditional expression.
--
-- > mux test onTrue onFalse
mux :: AllE a => E Bool -> E a -> E a -> E a
mux = Mux

-- | Creates a hierarchical scope.
scope :: Name -> Stmt a -> Stmt a
scope name (Stmt f0) = Stmt f1
  where
  f1 (path, statement) = (a, (path, statement1))
    where
    (a, (_, statement1)) = f0 (path ++ [name], statement)
  
get :: Stmt ([Name], Statement)
get = Stmt $ \ a -> (a, a)

getPath :: Stmt [Name]
getPath = do
  (path, _) <- get
  return path

var :: AllE a => Name -> a -> Stmt (V a)
var name init = do
  path <- getPath
  return $ V False (path ++ [name]) init

-- | Input variable declaration.  Input variables are initialized to 0.
input  :: AllE a => (Name -> a -> Stmt (V a)) -> Name -> Stmt (E a)
input f name = do
  path <- getPath
  return $ ref $ V True (path ++ [name]) $ zero f

-- | Boolean variable declaration.
bool :: Name -> Bool -> Stmt (V Bool)
bool = var

-- | Boolean variable declaration and immediate assignment.
bool' :: Name -> E Bool -> Stmt (E Bool)
bool' name value = do
  a <- bool name False
  a <== value
  return $ ref a

-- | Int variable declaration.
int :: Name -> Int -> Stmt (V Int)
int = var

-- | Int variable declaration and immediate assignment.
int' :: Name -> E Int -> Stmt (E Int)
int' name value = do
  a <- int name 0
  a <== value
  return $ ref a

-- | Float variable declaration.
float :: Name -> Float -> Stmt (V Float)
float = var

-- | Float variable declaration and immediate assignment.
float' :: Name -> E Float -> Stmt (E Float)
float' name value = do
  a <- float name 0
  a <== value
  return $ ref a

-- | Increments an E Int.
incr :: V Int -> Stmt ()
incr a = a <== ref a + 1

-- | Decrements an E Int.
decr :: V Int -> Stmt ()
decr a = a <== ref a - 1

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
statement a = Stmt $ \ (path, statement) -> ((), (path, Sequence statement a))

evalStmt :: [Name] -> Stmt () -> ([Name], Statement)
evalStmt path (Stmt f) = snd $ f (path, Null)

class    Assign a     where (<==) :: V a -> E a -> Stmt ()
instance Assign Bool  where a <== b = statement $ AssignBool  a b
instance Assign Int   where a <== b = statement $ AssignInt   a b
instance Assign Float where a <== b = statement $ AssignFloat a b

-- | Assert that a condition is true.
assert :: Name -> E Bool -> Stmt ()
assert a b = do
  path <- getPath
  statement $ Assert (path ++ [a]) b

-- | Declare an assumption condition is true.
assume :: Name -> E Bool -> Stmt ()
assume a b = do
  path <- getPath
  statement $ Assume (path ++ [a]) b

-- | Conditional if-else.
ifelse :: Name -> E Bool -> Stmt () -> Stmt () -> Stmt ()
ifelse name cond onTrue onFalse = do
  path <- getPath
  let (_, stmt1) = evalStmt path onTrue
      (_, stmt2) = evalStmt path onFalse
  statement $ Branch (path ++ [name]) cond stmt1 stmt2

-- | Conditional if without the else.
if_ :: Name -> E Bool -> Stmt () -> Stmt()
if_ name cond stmt = ifelse name cond stmt $ return ()

-- | Verify a program.
--
-- ^ verify pathToYices maxK program
verify :: FilePath -> Int -> Stmt () -> IO ()
verify yices maxK program = V.verify yices maxK $ snd $ evalStmt [] program

-- | Generate C code.
code :: Name -> Stmt () -> IO ()
code name program = C.code name $ snd $ evalStmt [name ++ "Variables"] program

