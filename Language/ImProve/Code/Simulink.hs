module Language.ImProve.Code.Simulink (codeSimulink) where

import Control.Monad.State
import Data.List
import Data.Maybe

import Language.ImProve.Code.Common
import Language.ImProve.Core

infixr 0 :-, :=

showConst :: Const -> String
showConst a = case a of
  Bool  True  -> "1"
  Bool  False -> "0"
  Int   a     -> show a
  Float a     -> show a

type Net = StateT Netlist IO

data Block
  = Inport  Const
  | Outport Const
  | UnitDelay Const
  | Cast String
  | Assertion
  | Const' Const
  | Add'
  | Sub'
  | Mul'
  | Div'
  | Mod'
  | Not'
  | And'
  | Or'
  | Eq'
  | Lt'
  | Gt'
  | Le'
  | Ge'
  | Mux'

data Netlist = Netlist
  { nextId :: Int
  , path   :: Path
  , vars   :: [Path]
  , env    :: [Name]
  , blocks :: [(Name, Block)]
  , nets   :: [(Name, (Name, Int))]
  }

-- Simulink generation.
codeSimulink :: Name -> Statement -> IO ()
codeSimulink name stmt' = do
  net <- execStateT all (Netlist 0 [] paths env [] []) >>= return . removeNullEffect
  writeFile (name ++ ".mdl") $ show $ mdl name $ (mdlBlocks $ blocks net) ++ (mdlLines $ nets net)
  where
  stmt = lowerConditionals (Const True) stmt'
  vars = stmtVars stmt
  paths = [ path | (_, path, _) <- vars ]
  env = [ error $ "variable " ++ pathName a ++ " does not have a source" | a <- vars ]

  all :: Net ()
  all = do
    inputs <- mapM input vars
    evalStmt stmt
    mapM_ output $ zip vars inputs

  input :: VarInfo -> Net Name
  input (input, path, const) = if input
    then do
      a <- block' (pathName path) (Inport const)
      updateEnv path a
      return a
    else do
      a <- block $ UnitDelay const
      b <- block $ Cast $ constType const
      net a (b, 0)
      updateEnv path b
      return a
  
  output :: (VarInfo, Name) -> Net ()
  output ((True, _, _), _) = return ()
  output ((False, path, const), delay) = do
    a <- block' (pathName path) $ Outport const
    src <- getNet path
    net src (a, 0)
    net src (delay, 0)

-- Pushes conditionals down to theorems and assumptions.
lowerConditionals :: E Bool -> Statement -> Statement
lowerConditionals cond a = case a of
  Assign   a b     -> Assign a b
  Branch   a b c   -> Branch a (lowerConditionals (And cond a) b) (lowerConditionals (And cond $ Not a) c)
  Sequence a b     -> Sequence (lowerConditionals cond a) (lowerConditionals cond b)
  Theorem  a b c d -> Theorem a b c $ Or (Not cond) d
  Assume   a       -> Assume $ Or (Not cond) a
  Label    a b     -> Label a $ lowerConditionals cond b
  Null             -> Null

newName :: Net Name
newName = do
  net <- get
  put net { nextId = nextId net + 1 }
  return $ "b" ++ show (nextId net)

-- New unnamed block.
block :: Block -> Net Name
block a = do
  name <- newName
  modify $ \ net -> net { blocks = (name, a) : blocks net }
  return name

-- New named block.
block' :: Name -> Block -> Net Name
block' name a = do
  modify $ \ net -> net { blocks = (name, a) : blocks net }
  return name

-- New net.
net :: Name -> (Name, Int) -> Net ()
net src (dest, port) = modify $ \ net -> net { nets = (src, (dest, port)) : nets net }

updateEnv :: Path -> Name -> Net ()
updateEnv path name = do
  net <- get
  let i = fromJust $ elemIndex path $ vars net
      pre = take i $ env net
      post = drop (i + 1) $ env net
  put net { env = pre ++ [name] ++ post }

getNet :: Path -> Net Name
getNet path = do
  net <- get
  return $ env net !! (fromJust $ elemIndex path $ vars net)

getPathName :: Net Name
getPathName = do
  net <- get
  return $ pathName $ path net

-- Elaborate netlist.
evalStmt :: Statement -> Net ()
evalStmt a = case a of 

  Assign (V _ path _) b -> do
    b <- evalExpr b
    updateEnv path b

  Branch a b c -> do
    cond <- evalExpr a
    net0 <- get

    evalStmt b
    net1 <- get
    modify $ \ net -> net { env = env net0 }

    evalStmt c
    net2 <- get
    modify $ \ net -> net { env = env net0 }

    names <- mergeEnvs cond (env net1) (env net2)
    modify $ \ net -> net { env = names }

    where

    mergeEnvs :: Name -> [Name] -> [Name] -> Net [Name]
    mergeEnvs _ [] [] = return []
    mergeEnvs cond (a : as) (b : bs) = do
      names <- mergeEnvs cond as bs
      name <- if a == b then return a else do
        switch <- block Mux'
        net a    (switch, 0)
        net cond (switch, 1)
        net b    (switch, 2)
        return switch
      return $ name : names
    mergeEnvs _ _ _ = error "unbalanced environments"

  Sequence a b    -> evalStmt a >> evalStmt b

  Theorem _ _ _ a -> do
    a <- evalExpr a
    name <- getPathName
    assert <- block' name Assertion
    net a (assert, 0)

  Assume a -> do
    a <- evalExpr a
    name <- getPathName
    assert <- block' name Assertion
    net a (assert, 0)

  Label name a -> do
    modify $ \ net -> net { path = path net ++ [name] }
    evalStmt a
    modify $ \ net -> net { path = init $ path net }

  Null            -> return ()

evalExpr :: E a -> Net Name
evalExpr a = case a of
  Ref (V _ path _) -> getNet path
  Const a   -> block $ Const' $ const' a
  Add a b   -> f2 Add' a b
  Sub a b   -> f2 Sub' a b
  Mul a b   -> do
    b <- block $ Const' $ const' b
    f2' Mul' a b
  Div a b   -> do
    b <- block $ Const' $ const' b
    f2' Div' a b
  Mod a b   -> do
    b <- block $ Const' $ const' b
    f2' Mod' a b
  Not a     -> f1 Not' a
  And a b   -> f2 And' a b
  Or  a b   -> f2 Or'  a b
  Eq  a b   -> f2 Eq'  a b
  Lt  a b   -> f2 Lt'  a b
  Gt  a b   -> f2 Gt'  a b
  Le  a b   -> f2 Le'  a b
  Ge  a b   -> f2 Ge'  a b
  Mux a b c -> f3 Mux' b a c
  where
  f1 :: Block -> E a -> Net Name
  f1 b a1 = do
    a1 <- evalExpr a1
    b  <- block b
    net a1 (b, 0)
    return b

  f2 :: Block -> E a -> E b -> Net Name
  f2 b a1 a2 = do
    a1 <- evalExpr a1
    a2 <- evalExpr a2
    b  <- block b
    net a1 (b, 0)
    net a2 (b, 1)
    return b

  f2' :: Block -> E a -> Name -> Net Name
  f2' b a1 a2 = do
    a1 <- evalExpr a1
    b  <- block b
    net a1 (b, 0)
    net a2 (b, 1)
    return b

  f3 :: Block -> E a -> E b -> E c -> Net Name
  f3 b a1 a2 a3 = do
    a1 <- evalExpr a1
    a2 <- evalExpr a2
    a3 <- evalExpr a3
    b  <- block b
    net a1 (b, 0)
    net a2 (b, 1)
    net a3 (b, 2)
    return b

data Mdl
  = String :- String
  | String := [Mdl]

instance Show Mdl where
  show a = case a of
    name :- value -> name ++ "\t" ++ show value ++ "\n"
    name := items -> name ++ " {\n" ++ indent (concatMap show items) ++ "}\n"

mdl :: Name -> [Mdl] -> Mdl
mdl name blocks = "Library" :=
  [ "Name" :- name
  , "System" :=
    [ "Name" :- name
    , "Block" :=
      [ "BlockType" :- "SubSystem"
      , "Name" :- name
      , "TreatAsAtomicUnit" :- "on"
      , "System" := ("Name" :- name) : blocks
      ]
    ]
  ]

mdlLines :: [(Name, (Name, Int))] -> [Mdl]
mdlLines nets = map branch branches
  where
  branches :: [(Name, [(Name, Int)])]
  branches = [ (src, [ dest | (src', dest) <- nets, src == src' ]) | src <- nub $ fst $ unzip nets ]
  branch :: (Name, [(Name, Int)]) -> Mdl
  branch (src, dests) = "Line" :=
    [ "SrcBlock" :- src
    , "SrcPort"  :- "1"
    ] ++ (if length dests == 1 then head dests' else map ("Branch" :=) dests')
    where
    dests' = [ ["DstBlock" :- dest, "DstPort" :- show $ port + 1] | (dest, port) <- dests ]

mdlBlocks :: [(Name, Block)] -> [Mdl]
mdlBlocks blocks = map (port "Inport") inputs ++ map blk others ++ map (port "Outport") outputs
  where
  inputs  = zip [1 ..] $ sortBy (\ (a, _) (b, _) -> compare a b) [ (name, constType init) | (name, Inport  init) <- blocks ]
  outputs = zip [1 ..] $ sortBy (\ (a, _) (b, _) -> compare a b) [ (name, constType init) | (name, Outport init) <- blocks ]
  others  = [ (name, block) | (name, block) <- blocks, not $ isPort block ]
  port :: String -> (Int, (Name, String)) -> Mdl
  port direction (port, (name, typ)) = mdlBlock direction name
    [ "Port" :- show port
    , "DataType" :- typ
    ]
  isPort :: Block -> Bool
  isPort (Inport  _) = True
  isPort (Outport _) = True
  isPort _           = False

mdlBlock :: String -> Name -> [Mdl] -> Mdl
mdlBlock blockType name fields = "Block" :=
  [ "BlockType" :- blockType
  , "Name"      :- name
  ] ++ fields

constType :: Const -> String
constType a = case a of
  Bool  _ -> "boolean"
  Int   _ -> "int32"
  Float _ -> "single"

blk :: (Name, Block) -> Mdl
blk (name, a) = case a of
  Inport  _ -> undefined
  Outport _ -> undefined
  UnitDelay init -> f "UnitDelay"          ["X0" :- showConst init, "SampleTime" :- "-1"]
  Cast t         -> f "DataTypeConversion" ["OutDataTypeMode" :- t]
  Assertion      -> f "Assertion"          ["StopWhenAssertionFail" :- "off", "SampleTime" :- "-1", "Enabled" :- "on"]
  Const' c       -> f "Constant"           ["Value" :- showConst c, "OutDataTypeMode" :- constType c]
  Add'           -> f "Sum"                ["Inputs" :- "++"]
  Sub'           -> f "Sum"                ["Inputs" :- "+-"]
  Mul'           -> f "Product"            ["Inputs" :- "**"]
  Div'           -> f "Product"            ["Inputs" :- "*/"]
  Mod'           -> f "Math"               ["Operator" :- "mod"]
  Not'           -> f "Logic"              ["Operator" :- "NOT", "Inputs" :- "1"]
  And'           -> f "Logic"              ["Operator" :- "AND", "Inputs" :- "2"]
  Or'            -> f "Logic"              ["Operator" :- "OR",  "Inputs" :- "2"]
  Eq'            -> f "RelationalOperator" ["Operator" :- "==", "LogicOutDataTypeMode" :- "boolean"]
  Lt'            -> f "RelationalOperator" ["Operator" :- "<" , "LogicOutDataTypeMode" :- "boolean"]
  Gt'            -> f "RelationalOperator" ["Operator" :- ">" , "LogicOutDataTypeMode" :- "boolean"]
  Le'            -> f "RelationalOperator" ["Operator" :- "<=", "LogicOutDataTypeMode" :- "boolean"]
  Ge'            -> f "RelationalOperator" ["Operator" :- ">=", "LogicOutDataTypeMode" :- "boolean"]
  Mux'           -> f "Switch"             ["Criteria" :- "u2 ~= 0"]
  where
  f typ args = mdlBlock typ name args

isSrc :: Block -> Bool
isSrc a = case a of
  Outport _ -> False
  Assertion -> False
  _         -> True

removeNullEffect :: Netlist -> Netlist
removeNullEffect net = if null unused then net else removeNullEffect net { blocks = blocks', nets = nets' }
  where
  unused = [ name | (name, block) <- blocks net, isSrc block, not $ any (\ (n, _) -> name == n) $ nets net ]
  blocks' = [ (name, block) | (name, block) <- blocks net, not $ elem name unused ]
  nets' = [ (src, (dest, port)) | (src, (dest, port)) <- nets net, not $ elem dest unused ]

