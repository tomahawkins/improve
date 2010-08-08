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
  -- * Compilation
  , compile
  ) where

import Control.Monad
import Data.List
import Text.Printf

import Language.ImProve.Core
import qualified Language.ImProve.Verify as V

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
  f1 (path, items, statement) = (a, (path, Scope name items0 : items, statement1))
    where
    (a, (_, items0, statement1)) = f0 (path ++ [name], [], statement)
  
get :: Stmt ([Name], [Scope], Statement)
get = Stmt $ \ a -> (a, a)

getPath :: Stmt [Name]
getPath = do
  (path, _, _) <- get
  return path

put :: ([Name], [Scope], Statement) -> Stmt ()
put a = Stmt $ \ _ -> ((), a)

var :: AllE a => Name -> a -> Stmt (V a)
var name init = do
  (path, items, stmt) <- get
  put (path, Variable False name (showType init) (showConst init) : items, stmt)
  return $ V (path ++ [name]) init

-- | Input variable declaration.  Input variables are initialized to 0.
input  :: AllE a => (Name -> a -> Stmt (V a)) -> Name -> Stmt (E a)
input f name = do
  (path, items, stmt) <- get
  put (path, Variable True name (showType $ zero f) (showConst $ zero f) : items, stmt)
  return $ ref $ VIn (path ++ [name])

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
data Stmt a = Stmt (([Name], [Scope], Statement) -> (a, ([Name], [Scope], Statement)))

instance Monad Stmt where
  return a = Stmt $ \ s -> (a, s)
  (Stmt f1) >>= f2 = Stmt f3
    where
    f3 s1 = f4 s2
      where
      (a, s2) = f1 s1
      Stmt f4 = f2 a

statement :: Statement -> Stmt ()
statement a = Stmt $ \ (path, scope, statement) -> ((), (path, scope, Sequence statement a))

evalStmt :: [Name] -> [Scope] -> Stmt () -> ([Name], [Scope], Statement)
evalStmt path items (Stmt f) = snd $ f (path, items, Null)

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
ifelse :: E Bool -> Stmt () -> Stmt () -> Stmt ()
ifelse cond onTrue onFalse = do
  (path, items, stmt) <- get
  let (_, items1, stmt1) = evalStmt path items  onTrue
      (_, items2, stmt2) = evalStmt path items1 onFalse
  put (path, items2, stmt)
  statement $ Branch cond stmt1 stmt2

-- | Conditional if without the else.
if_ :: E Bool -> Stmt () -> Stmt()
if_ cond stmt = ifelse cond stmt $ return ()

-- | Verify a program.
verify :: Stmt () -> IO (Maybe Bool)
verify program = V.verify stmt
  where
  (_, _, stmt) = evalStmt [] [] program

-- | Generate C code.
compile :: Name -> Stmt () -> IO ()
compile name program = do
  writeFile (name ++ ".c") $
       "// Generated by ImProve.\n\n"
    ++ "#include <assert.h>\n\n"
    ++ codeVariables True scope ++ "\n"
    ++ "void " ++ name ++ "() {\n"
    ++ indent (codeStmt stmt)
    ++ "}\n\n"
  writeFile (name ++ ".h") $
       "// Generated by ImProve.\n\n"
    ++ codeVariables False scope ++ "\n"
    ++ "void " ++ name ++ "(void);\n\n"
  where
  (_, items, stmt) = evalStmt [name ++ "Variables"] [] program
  scope = Scope (name ++ "Variables") items

varName :: V a -> String
varName a = intercalate "." names
  where
  names = case a of
    V   names _ -> names
    VIn names   -> names

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

indent' :: String -> String
indent' a = case lines a of
  [] -> []
  (a:b) -> a ++ "\n" ++ indent (unlines b)

data Scope
  = Scope Name [Scope]
  | Variable Bool Name String String  -- input name type init
  deriving Eq

instance Ord Scope where
  compare a b = case (a, b) of
    (Scope a _, Scope b _) -> compare a b
    (Variable _ a _ _, Variable _ b _ _) -> compare a b
    (Variable _ _ _ _, Scope _ _) -> LT
    (Scope _ _, Variable _ _ _ _) -> GT

codeVariables :: Bool -> Scope -> String
codeVariables define a = (if define then "" else "extern ") ++ init (init (f1 a)) ++ (if define then " =\n  " ++ f2 a else "") ++ ";\n"
  where
  f1 a = case a of
    Scope     name items -> "struct {  // " ++ name ++ "\n" ++ indent (concatMap f1 $ sort items) ++ "} " ++ name ++ ";\n"
    Variable  input name typ _ -> printf "%-5s %-25s;%s\n" typ name (if input then "  // input" else "")

  f2 a = case a of
    Scope    name items -> indent' $ "{ " ++ (intercalate ", " $ map f2 $ sort items) ++ "}  // " ++ name ++ "\n"
    Variable _ name _ init -> printf "%-15s  // %s\n" init name

