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
  , (*.)
  , (/.)
  , mod_
  -- ** Conditional Operator
  , mux
  -- ** Lookups
  , linear
  -- * Hierarchical Scope
  , scope
  -- * Variable Declarations
  , bool
  , bool'
  , int
  , int'
  , float
  , float'
  , input
  -- * Statements
  , Stmt
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
  -- * Compilation
  , compile
  ) where

import Control.Monad
import Data.List
import Data.Ratio

infixl 7 *., /., `mod_`
infix  4 ==., /=., <., <=., >., >=.
infixl 3 &&.
infixl 2 ||.
infixr 1 <==

type Name = String

-- | Variables.
data V a
  = V   [Name] a
  | VIn [Name]

-- | All types.
class AllE a where
  showConst :: a -> String
  showType  :: a -> String

instance AllE Bool where
  showConst a = case a of
    True  -> "1"
    False -> "0"

  showType _ = "int"

instance AllE Int where
  showConst = show
  showType _ = "int"
  
instance AllE Float where
  showConst = show
  showType _ = "float"

-- | Number types.
class    AllE a => NumE a
instance NumE Int
instance NumE Float

-- | Core expressions.
data E a where
  Ref   :: V a -> E a
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
  Mux   :: E Bool -> E a -> E a -> E a

instance Show (E a) where show = undefined 
instance Eq   (E a) where (==) = undefined

instance (Num a, AllE a, NumE a) => Num (E a) where
  (+) = Add
  (-) = Sub
  (*) = error "general multiplication not supported, use (*.)"
  negate a = 0 - a
  abs a = mux (a <. 0) (negate a) a
  signum a = mux (a ==. 0) 0 $ mux (a <. 0) (-1) 1
  fromInteger = Const . fromInteger

instance Fractional (E Float) where
  (/) = error "general division not supported, use (/.)"
  recip a = 1 / a
  fromRational r = Const $ fromInteger (numerator r) / fromInteger (denominator r)

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

-- | Division.
(/.) :: NumE a => E a -> a -> E a
(/.) = Div

-- | Modulo.
mod_ :: E Int -> Int -> E Int
mod_ = Mod

-- | Linear interpolation and extrapolation between two points.
linear :: (Float, Float) -> (Float, Float) -> E Float -> E Float
linear (x1, y1) (x2, y2) a = a *. slope + constant inter
  where
  slope = (y2 - y1) / (x2 - x1)
  inter = y1 - slope * x1

-- | References a variable.
ref :: V a -> E a
ref = Ref

-- | Conditional expression.
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

-- | Input variable declaration.  Input variables are initialized to 0.
input  :: (Name -> a -> Stmt (V a)) -> Name -> Stmt (E a)
input _ name = do
  scope <- getScope
  return $ ref $ VIn (scope ++ [name])

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

-- | Conditional if-else.
ifelse :: E Bool -> Stmt () -> Stmt () -> Stmt ()
ifelse cond onTrue onFalse = do
  scope <- getScope
  statement $ Branch cond (evalStmt scope onTrue) (evalStmt scope onFalse)

-- | Conditional without the else.
if_ :: E Bool -> Stmt () -> Stmt()
if_ cond stmt = ifelse cond stmt $ return ()

-- | Generate C code.
compile :: Name -> Stmt () -> IO ()
compile name program = do
  writeFile (name ++ ".c") $
       "// Generated by ImProve.\n\n"
    ++ "#include <assert.h>\n\n"
    ++ "// XXX Need to build state struct.\n\n"
    ++ "void " ++ name ++ "() {\n"
    ++ indent (codeStmt stmt)
    ++ "}\n\n"
  writeFile (name ++ ".h") $
       "// Generated by ImProve.\n\n"
    ++ "// XXX Need to build state struct.\n\n"
    ++ "void " ++ name ++ "(void);\n\n"
  where
  stmt = evalStmt [] program

  varName :: V a -> String
  varName a = intercalate "." $ (name ++ "Variables") : names
    where
    names = case a of
      V names _ -> names
      VIn names -> names
  
  codeStmt :: Statement -> String
  codeStmt a = case a of
    AssignBool  a b -> varName a ++ " = " ++ codeExpr b ++ ";\n"
    AssignInt   a b -> varName a ++ " = " ++ codeExpr b ++ ";\n"
    AssignFloat a b -> varName a ++ " = " ++ codeExpr b ++ ";\n"
    Branch a b Null -> "if (" ++ codeExpr a ++ ") {\n" ++ indent (codeStmt b) ++ "}\n"
    Branch a b c    -> "if (" ++ codeExpr a ++ ") {\n" ++ indent (codeStmt b) ++ "}\nelse {\n" ++ indent (codeStmt c) ++ "}\n"
    Sequence a b -> codeStmt a ++ codeStmt b
    Assert names a -> "// assert " ++ intercalate "." names ++ "\nassert(" ++ codeExpr a ++ ");\n"
    Assume names a -> "// assume " ++ intercalate "." names ++ "\nassert(" ++ codeExpr a ++ ");\n"
    Null -> ""
  
  codeExpr :: E a -> String
  codeExpr a = case a of
    Ref a -> varName a
    Const a -> showConst a
    Add a b -> group [codeExpr a, "+", codeExpr b]
    Sub a b -> group [codeExpr a, "-", codeExpr b]
    Mul a b -> group [codeExpr a, "*", showConst b]
    Div a b -> group [codeExpr a, "/", showConst b]
    Mod a b -> group [codeExpr a, "%", showConst b]
    Not a   -> group ["!", codeExpr a]
    And a b -> group [codeExpr a, "&&",  codeExpr b]
    Or  a b -> group [codeExpr a, "||",  codeExpr b]
    Eq  a b -> group [codeExpr a, "==",  codeExpr b]
    Lt  a b -> group [codeExpr a, "<",   codeExpr b]
    Gt  a b -> group [codeExpr a, ">",   codeExpr b]
    Le  a b -> group [codeExpr a, "<=",  codeExpr b]
    Ge  a b -> group [codeExpr a, ">=",  codeExpr b]
    Mux a b c -> group [codeExpr a, "?", codeExpr b, ":", codeExpr c] 
    where
    group :: [String] -> String
    group a = "(" ++ intercalate " " a ++ ")"


indent :: String -> String
indent = unlines . map ("  " ++) . lines

