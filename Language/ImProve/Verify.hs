module Language.ImProve.Verify (verify) where

import Control.Monad.State hiding (State)
import Math.SMT.Yices.Pipe
import Math.SMT.Yices.Syntax
import System.IO
import Text.Printf

import Language.ImProve.Core

-- | Verify a program with k-induction.
verify :: FilePath -> Int -> Statement -> IO ()
verify _ maxK _ | maxK < 1 = error "max k can not be less than 1"
verify yices maxK program = do
  mapM_ (verifyProgram yices format maxK) $ trimAssertions program
  where
  format = "verifying %-" ++ show (maximum [ length $ pathName path | path <- assertions program ]) ++ "s    "

-- | Set of statements containing only one assertion.
trimAssertions :: Statement -> [Statement]
trimAssertions program = [ a | a <- trimAssertions' program, length (assertions a) == 1 ]

trimAssertions' :: Statement -> [Statement]
trimAssertions' a = case a of
  Sequence a b -> [ Sequence a (removeAssertions b) | a <- trimAssertions' a ]
               ++ [ Sequence (removeAssertions a) b | b <- trimAssertions' b ]
  Branch path cond a b -> [ Branch path cond a (removeAssertions b) | a <- trimAssertions' a ]
                       ++ [ Branch path cond (removeAssertions a) b | b <- trimAssertions' b ]
  Annotate name a -> [ Annotate name a | a <- trimAssertions a ]
  a -> [a]

-- | Remove all assertions.
removeAssertions :: Statement -> Statement
removeAssertions a = case a of
  Assert _ _ -> Null
  Sequence a b -> Sequence (removeAssertions a) (removeAssertions b)
  Branch path cond a b -> Branch path cond (removeAssertions a) (removeAssertions b)
  Annotate name a -> Annotate name $ removeAssertions a
  a -> a

-- | Paths of all assertions.
assertions :: Statement -> [Path]
assertions a = case a of
  Assert path _  -> [path]
  Sequence a b   -> assertions a ++ assertions b
  Branch _ _ a b -> assertions a ++ assertions b
  Annotate _ a   -> assertions a
  _ -> []

-- | Trim all unneeded stuff from a program.
trimProgram :: Statement -> Statement
trimProgram = id --XXX

-- | Verify a trimmed program.
verifyProgram :: FilePath -> String -> Int -> Statement -> IO ()
verifyProgram yices format maxK program' = do
  printf format name
  hFlush stdout
  env0 <- initEnv program
  execStateT (check yices name maxK program env0 1) env0
  return ()
  where
  program = trimProgram program'
  name = pathName $ head' "a1" $ assertions program

head' msg a = if null a then error msg else head a

data Result = Pass | Fail [ExpY] | Problem

-- | k-induction.
check :: FilePath -> Name -> Int -> Statement -> Env -> Int -> Y ()
check yices name maxK program env0 k = do
  addTrace $ Cycle' $ k - 1
  inputs program
  evalStmt (LitB True) program
  resultBasis <- checkBasis yices program env0
  case resultBasis of
    Fail a  -> liftIO (printf "FAILED: disproved basis in k = %d (see trace)\n" k) >> writeTrace name a
    Problem -> error "Verify.check1"
    Pass -> do
      resultStep <- checkStep yices
      case resultStep of
        Fail a | k < maxK  -> check yices name maxK program env0 (k + 1)
               | otherwise -> liftIO (printf "inconclusive: unable to proved step up to max k = %d (see trace)\n" k) >> writeTrace name a
        Problem -> error "Verify.check2"
        Pass    -> liftIO $ printf "passed: proved step in k = %d\n" k
        
-- | Check induction step.
checkStep :: FilePath -> Y Result
checkStep yices = do
  env <- get
  r <- liftIO $ quickCheckY' yices [] $ reverse (cmds env) ++ [ASSERT $ NOT $ head' "a2" $ asserts env] ++ [CHECK]
  return $ result r

-- | Check induction basis.
checkBasis :: FilePath -> Statement -> Env -> Y Result
checkBasis yices program env0 = do
  env <- get
  r <- liftIO $ quickCheckY' yices [] $ reverse (cmds env)
          ++ [ASSERT $ NOT $ AND $ asserts env]
          ++ [ ASSERT $ VarE (var env0 a) := evalConst' c | a@(input, _, c) <- stmtVars program, not input ]
          ++ [CHECK]
  return $ result r

-- | Insert new input variables.
inputs :: Statement -> Y ()
inputs program = sequence_ [ addVar' a >>= addTrace . Input' (pathName path) | a@(input, path, _) <- stmtVars program, input ]

result :: ResY -> Result
result a = case a of
  Sat a   -> Fail a
  UnSat _ -> Pass
  InCon _ -> Problem
  _ -> error $ "unexpected yices results: " ++ show a


evalStmt :: ExpY -> Statement -> Y ()
evalStmt enabled a = case a of
  Null -> return ()
  Sequence a b -> evalStmt enabled a >> evalStmt enabled b
  AssignBool  a b -> assign a b
  AssignInt   a b -> assign a b
  AssignFloat a b -> assign a b
  Assert path a -> do
    a <- evalExpr a
    b <- newBoolVar
    addCmd $ ASSERT (VarE b := (enabled :=> a))
    env <- get
    put env { asserts = VarE b : asserts env }
    addTrace $ Assert' (pathName path) b
  Assume _ a -> do
    a <- evalExpr a
    addCmd $ ASSERT (enabled :=> a)
  Branch path a onTrue onFalse -> do
    a <- evalExpr a
    b <- newBoolVar
    addCmd $ ASSERT (VarE b := a)
    env0 <- get
    put env0 { trace = [] }
    evalStmt (AND [enabled, a]) onTrue
    env1 <- get
    put env1 { trace = [] }
    evalStmt (AND [enabled, NOT a]) onFalse
    env2 <- get
    put env2 { trace = Branch' (pathName path) b (reverse $ trace env1) (reverse $ trace env2) : trace env0 }
  Annotate name a -> do
    env0 <- get
    put env0 { trace = [] }
    evalStmt enabled a
    env1 <- get
    put env1 { trace = Annotate' name (reverse $ trace env1) : trace env0 }
  where
  assign :: AllE a => V a -> E a -> Y ()
  assign a b = do
    b <- evalExpr b
    aPrev <- getVar a
    aNext <- addVar a
    addCmd $ ASSERT (VarE aNext := IF enabled b (VarE aPrev))
    addTrace $ Assign' (pathName a) aNext

evalExpr :: AllE a => E a -> Y ExpY
evalExpr a = case a of
  Ref a -> getVar a >>= return . VarE
  Const a -> return $ evalConst a
  Add a b ->  do
    a <- evalExpr a
    b <- evalExpr b
    return $ a :+: b
  Sub a b ->  do
    a <- evalExpr a
    b <- evalExpr b
    return $ a :-: b
  Mul a b ->  do
    a <- evalExpr a
    return $ a :*: evalConst b
  Div a b -> do
    a <- evalExpr a
    return $ op a $ evalConst b
    where
    op = case const' b of
      Bool  _ -> undefined
      Int   _ -> DIV
      Float _ -> (:/:)
  Mod a b -> do
    a <- evalExpr a
    return $ MOD a $ evalConst b
  Not a -> evalExpr a >>= return . NOT
  And a b -> do
    a <- evalExpr a
    b <- evalExpr b
    return $ AND [a, b]
  Or a b -> do
    a <- evalExpr a
    b <- evalExpr b
    return $ OR [a, b]
  Eq a b -> do  
    a <- evalExpr a
    b <- evalExpr b
    return $ a := b
  Lt a b -> do  
    a <- evalExpr a
    b <- evalExpr b
    return $ a :< b
  Gt a b -> do  
    a <- evalExpr a
    b <- evalExpr b
    return $ a :> b
  Le a b -> do  
    a <- evalExpr a
    b <- evalExpr b
    return $ a :<= b
  Ge a b -> do  
    a <- evalExpr a
    b <- evalExpr b
    return $ a :>= b
  Mux a b c -> do
    a <- evalExpr a
    b <- evalExpr b
    c <- evalExpr c
    return $ IF a b c

evalConst :: AllE a => a -> ExpY
evalConst = evalConst' . const'

evalConst' :: Const -> ExpY
evalConst' a = case a of
  Bool  a -> LitB a
  Int   a -> LitI $ fromIntegral a
  Float a -> LitR $ toRational a

type Y = StateT Env IO

type Var = String

data Env = Env
  { nextId    :: Int
  , var       :: VarInfo -> Var
  , cmds      :: [CmdY]  -- Commands and variable declarations in reverse order.
  , asserts   :: [ExpY]  -- Assumes 1 assert in a program under verification.
  , trace     :: [Trace] -- Program trace in reverse order.
  }
 
initEnv :: Statement -> IO Env
initEnv program = execStateT (sequence_ [ addVar' a >>= addTrace . Init' (pathName path) | a@(input, path, _) <- stmtVars program, not input ]) Env
  { nextId  = 0
  , var     = \ v -> error $ "variable not found in environment: " ++ pathName v
  , cmds    = []
  , asserts = []
  , trace   = []
  }

data Trace
  = Init'     Name Var
  | Cycle'    Int
  | Input'    Name Var
  | Assign'   Name Var
  | Assert'   Name Var
  | Branch'   Name Var [Trace] [Trace] 
  | Annotate' Name [Trace]

addVar' :: VarInfo -> Y String
addVar' v = do
  env <- get
  let name = printf "n%d" $ nextId env
  put env { nextId = nextId env + 1, var = \ a -> if a == v then name else var env a, cmds = DEFINE (name, VarT typ) Nothing : cmds env }
  return name
  where
  typ = case v of
    (_, _, Bool  _) -> "bool"
    (_, _, Int   _) -> "int"
    (_, _, Float _) -> "real"

addVar :: AllE a => V a -> Y String
addVar = addVar' . varInfo

-- | Creates a new boolean variable.  Use for assertions.
newBoolVar :: Y String
newBoolVar = do
  env <- get
  let name = printf "n%d" $ nextId env
  put env { nextId = nextId env + 1, cmds = DEFINE (name, VarT "bool") Nothing : cmds env }
  return name

addCmd :: CmdY -> Y ()
addCmd cmd = do
  env <- get
  put env { cmds = cmd : cmds env }

addTrace :: Trace -> Y ()
addTrace t = do
  env <- get
  put env { trace = t : trace env }

getVar :: AllE a => V a -> Y String
getVar v = do
  env <- get
  return $ var env $ varInfo v

writeTrace :: String -> [ExpY] -> Y ()
writeTrace name table' = do
  env <- get
  liftIO $ writeFile (name ++ ".trace") $ concatMap f $ reverse $ trace env
  where
  table = [ (n, if v then "true" else "false") | VarE n := LitB v <- table' ]
       ++ [ (n, show v) | VarE n := LitI v <- table' ]
       ++ [ (n, show v) | VarE n := LitR v <- table' ]
  f :: Trace -> String
  f a = case a of
    Init' path var -> case lookup var table of
      Nothing -> ""
      Just value -> "initialize " ++ path ++ " <== " ++ value ++ "\n"
    Cycle' n -> "\nstep " ++ show n ++ "\n"
    Input' path var -> case lookup var table of
      Nothing -> ""
      Just value -> "input " ++ path ++ " <== " ++ value ++ "\n"
    Assign' path var -> case lookup var table of
      Nothing -> ""
      Just value -> path ++ " <== " ++ value ++ "\n"
    Assert' path var -> case lookup var table of
      Just "true"  -> "assertion passed: " ++ path ++ "\n"
      Just "false" -> "assertion FAILED: " ++ path ++ "\n"
      _ -> ""
    Branch' path cond onTrue onFalse -> case lookup cond table of
      Just "true"  -> "ifelse " ++ path ++ " true\n"  ++ indent (concatMap f onTrue)
      Just "false" -> "ifelse " ++ path ++ " false\n" ++ indent (concatMap f onFalse)
      _ -> ""
    Annotate' name traces -> "annotate " ++ name ++ "\n" ++ indent (concatMap f traces)

indent :: String -> String
indent = unlines . map ("    " ++) . lines

