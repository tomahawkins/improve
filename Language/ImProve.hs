{- |
ImProve is an imperative programming language for high assurance applications.

ImProve uses infinite state, unbounded model checking to verify programs
adhere to specifications, which are written in the form of assertion statements.
If it is unable to verify an assertion, ImProve will emit a counter example
that shows a precise program trace that exercises the assertion violation.

The following compares the syntax of C and ImProve:

/Variable Declarations/

@
float a = 0.0;            a <- 'float' \"a\" 0
bool b = true;            b <- 'bool' \"b\" True
int c = d + e + 3;        c <- 'int'' \"c\" (d + e + 3)
@

/Variable Assignments/

@
a = 1;                    a '<==' 1
@

/Conditional Statements/

@
if (condition) {          'if_' condition $ do 
    a();                      a
    b();                      b
    c();                      c
}

if (condition {           'ifelse' condition
    a();                      (do a
    b();                          b
    c();                          c)
}                             (do d
else {                            e 
    d();                          f)
    e();
    f();
}

switch (a) {              'case_' a
    case 1:                   [ (a ==. 1, do1)
        do1();                , (a ==. 2, do2)
        break;                , (true   , do3)
    case 2:                   ]
        do2();
        break;
    default:
        do3();
}
@

/Assertion Statements/

@
assert(condition);        'assert' condition
@

/Statement Labels/

@
label: {                  \"label\" '|-' do
    a();                      a
    b();                      b
}
@

/Expressions/

@
/Constant Literals/

true                      'true'
false                     'false'
0                         0
100                       100
1.0                       1     -- float
3.14                      3.14

/Variable Reference/

a                         'ref' a

/Logical Expressions/

! a                       'not_' a
a && b                    a '&&.' b
a || b                    a '||.' b

/Comparison Expressions/

a == b                    a '==.' b
a != b                    a '/=.' b
a < b                     a '<.' b
a > b                     a '>.' b
a <= b                    a '<=.' b
a >= b                    a '>=.' b

/Arithmetic Expressions/

a + b                     a '+' b
a * b                     a '*.' b
a \/ b                     a '/.' b     -- float
a \/ b                     'div_' a b   -- int
a % b                     'mod_' a b
abs(a)                    'abs' a
min(a, b)                 'min_' a b
max(a, b)                 'max_' a b

/Conditional Expression/

a ? b : c                 'mux' a b c
@

/Function Definitions and Function Calls/
(All ImProve functions are Haskell functions, which are inlined at code generation.)

@
int add(int a, int b) {                             add :: E Int -> E Int -> E Int
  return a + b;                                     add a b = a + b
}

three = add(1, 2);                                  three <== add 1 2

void incrCounter(int *counter, int amount) {        incrCounter :: V Int -> E Int -> Stmt ()
  *counter = *counter + amount;                     incrCounter counter amount = counter <== ref counter + amount
}

incrCounter(&counter, 22);                          incrCounter counter 22
@

-}

-- hello: \{                  hello '+++' do
--     a();                      a
--     b();                      b
--

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
  , (-->)
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
  -- * Statements
  , Stmt
  -- ** Variable Hierarchical Scope and Statement Labeling 
  , (|=)
  , (|-)
  , (|=-)
  -- ** Variable Declarations
  , bool
  , bool'
  , int
  , int'
  , float
  , float'
  , input
  -- ** Variable Assignment
  , Assign (..)
  -- ** Conditional Execution
  , ifelse
  , if_
  , case_
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
infixr 1 -->
infixr 0 <==, |=, |-, |=-

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

-- | Logical implication.
(-->) :: E Bool -> E Bool -> E Bool 
a --> b = not_ a ||. b

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

-- | References a variable to be used in an expression ('E').
ref :: AllE a => V a -> E a
ref = Ref

-- | Conditional expression.
--
-- > mux test onTrue onFalse
mux :: AllE a => E Bool -> E a -> E a -> E a
mux = Mux

-- | Labels a statement.
--   Labels are used in counter examples to trace the program execution.
--   And assertion names, and hence counter example trace file names, are produce from labels.
(|-) :: Name -> Stmt a -> Stmt a
name |- stmt = do
  (path0, stmt0) <- get
  put (path0, Null)
  a <- stmt
  (_, stmt1) <- get
  put (path0, stmt0)
  statement $ Label name stmt1
  return a

-- | Creates a new hierarchical scope for variable names.
(|=) :: Name -> Stmt a -> Stmt a
name |= stmt = do
  (path0, stmt0) <- get
  put (path0 ++ [name], stmt0)
  a <- stmt
  (_, stmt1) <- get
  put (path0, stmt1)
  return a

-- | Creates a new hierarchical scope and labels a statement with the same name.
(|=-) :: Name -> Stmt a -> Stmt a
name |=- stmt = name |= name |- stmt

get :: Stmt ([Name], Statement)
get = Stmt $ \ a -> (a, a)

put :: ([Name], Statement) -> Stmt ()
put s = Stmt $ \ _ -> ((), s)

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

class Assign a where
  (<==) :: V a -> E a -> Stmt ()
instance Assign Bool  where a <== b = statement $ AssignBool  a b
instance Assign Int   where a <== b = statement $ AssignInt   a b
instance Assign Float where a <== b = statement $ AssignFloat a b

-- | Assert that a condition is true.
assert :: E Bool -> Stmt ()
assert = statement . Assert

-- | Declare an assumption condition is true.
--   Assumptions expressions must contain variables directly or indirectly related
--   to the assertion under verification, otherwise they will be ignored.
assume :: E Bool -> Stmt ()
assume a = statement $ Assume a

-- | Conditional if-else.
ifelse :: E Bool -> Stmt () -> Stmt () -> Stmt ()
ifelse cond onTrue onFalse = do
  path <- getPath
  let (_, stmt1) = evalStmt path onTrue
      (_, stmt2) = evalStmt path onFalse
  statement $ Branch cond stmt1 stmt2

-- | Conditional if without the else.
if_ :: E Bool -> Stmt () -> Stmt()
if_ cond stmt = ifelse cond stmt $ return ()

-- | Condition case statement.
case_ :: [(E Bool, Stmt ())] -> Stmt ()
case_ [] = return ()
case_ ((cond, action) : b) = ifelse cond action $ case_ b

-- | Verify a program.
--
-- ^ verify pathToYices maxK program
verify :: FilePath -> Int -> Stmt () -> IO ()
verify yices maxK program = V.verify yices maxK $ snd $ evalStmt [] program

-- | Generate C code.
code :: Name -> Stmt () -> IO ()
code name program = C.code name $ snd $ evalStmt [name ++ "Variables"] program

