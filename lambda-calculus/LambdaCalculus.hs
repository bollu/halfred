{-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat
-}

-- This file implements a partial evaluator for the lambda calculus with a fixpoint
-- operator. We impement the NBE phase of the partial evaluator in the style of
-- a shallow embedding, where we use metalanguage (Haskell) functions to build closures for
-- the embedded lambda calculus.

{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
import qualified Data.Map.Strict as M
import Control.Monad(ap)
import System.Environment
import System.Exit
import Data.List
import AST
import Data.Either
import Control.Monad(foldM)

type Var = String
-- Variables for locally nameless
-- data Var where
--   FVar :: Int -> Var
--   BVar :: Int -> Var


data Opcode where
    Add :: Opcode
    Sub :: Opcode
    Mul :: Opcode 
    CondEq :: Opcode

instance Show Opcode where 
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show CondEq = "=="

data Const where
    ConstInt :: Int -> Const
    ConstBool :: Bool -> Const

instance Show Const where 
    show (ConstInt i) = show i
    show (ConstBool b) = show b


data Stx where
  StxConst :: Const -> Stx
  StxVar :: Var -> Stx
  StxLam :: Var -> Stx -> Stx
  StxApp :: Stx -> Stx -> Stx
  StxIf :: Stx -> Stx -> Stx -> Stx
  StxOp :: Opcode -> [Stx] -> Stx

instance Show Stx where 
    show (StxConst c) = show c
    show (StxVar v) = v
    show (StxLam v e) = "(\\" ++ v ++ " " ++ show e ++ ")"
    show (StxApp e1 e2) = "(%" ++ show e1 ++ " " ++ show e2 ++ ")"
    show (StxIf e1 e2 e3) = "if " ++ show e1 ++ " " ++ show e2 ++ " " ++ show e3
    show (StxOp op es) = "(" ++ show op ++ " " ++ intercalate " " (map show es) ++ ")"
data Val where
    ValConst :: Const -> Val
    ValFun :: (Val -> EvalM Val) -> Val

instance Show Val where 
    show (ValConst c) = show c
    show (ValFun _) = "<fun>"
    
  
type EvalEnv = M.Map Var Val
data EvalError where 
  UnableToFindVarError :: Var -> EvalError
  ExpectedValFnError :: Const -> EvalError
  ExpectedValConstError :: Val -> EvalError
  UnknownStxError :: Stx -> EvalError

instance Show EvalError where 
  show (UnableToFindVarError v) = "UnableToFindVarError: " ++ v
  show (ExpectedValFnError c) = "ExpectedValFnError: " ++ show c
  show (ExpectedValConstError v) = "ExpectedValConstError: " ++ show v
  show (UnknownStxError s) = "UnknownStxError: " ++ show s

data EvalM a =
  EvalM {
    runEvalM :: EvalEnv -> (Either EvalError a, EvalEnv)
  } deriving(Functor)

evalLookupEnv :: Var -> EvalM Val
evalLookupEnv name =
  EvalM $ \env ->
    case M.lookup name env of
      Just val -> (Right val, env)
      Nothing -> (Left (UnableToFindVarError name), env)

evalInsertEnv :: Var -> Val -> EvalM ()
evalInsertEnv name val =
  EvalM $ \env -> (Right (), M.insert name val env)

evalError :: EvalError -> EvalM a
evalError err = EvalM $ \env -> (Left err, env)

instance Monad EvalM where
  return a = EvalM (\env -> (return a, env))
  ma >>= a2mb =
    EvalM (\env -> let (ea, env') = runEvalM ma env in
             case ea of
             Left e -> (Left e, env')
             Right a -> let mb = a2mb a in runEvalM mb env')

instance Applicative EvalM where
  pure = return
  (<*>) = ap

eval :: Stx -> EvalM Val
eval (StxConst c) = pure (ValConst c)
eval (StxVar v) = evalLookupEnv v
eval (StxLam xname body) =
  pure $ ValFun (\xval -> evalInsertEnv xname xval >> eval body)
eval (StxApp f x) = do
  vf <- eval f
  vx <- eval x
  case vf of
    ValConst c -> evalError (ExpectedValFnError c)
    ValFun f -> f vx
eval (StxIf cond t e) = do
  vcond <- eval cond
  case vcond of
    ValConst (ConstBool b) -> if b then eval t else eval e
    _ -> evalError (ExpectedValConstError vcond)
-- eval (StxOp [] )
eval stx = evalError (UnknownStxError stx)

data Decl = Decl {
  declLhs :: String,
  declRhs :: Stx
}

declEval :: Decl -> EvalM Val
declEval decl = do
  v <- eval (declRhs decl) -- evaluate
  evalInsertEnv (declLhs decl) v -- add to env
  return v -- return to toplevel

-- | Output of running a program.
data Output = Output { 
    outputErrors :: M.Map String EvalError 
    , outputValues :: M.Map String Val
    , outputEnv :: EvalEnv
}
-- | Note: the monoid takes the environment of the
-- | right output. This is because we want to evaluate
-- | expressions in order.
instance Monoid Output where
    mempty = Output M.empty M.empty M.empty
instance Semigroup Output where 
    (Output e1 v1 env1) <> (Output e2 v2 env2) 
      = Output (e1 <> e2) (v1 <> v2) env2 

instance Show Output where 
    show (Output errs vals env) = 
        "Errors: " ++ show errs ++
        "Outputs: " ++ show vals ++
        "Environment: " ++ show env
        
  
parseIntFromString :: String -> Maybe Int
parseIntFromString s = 
  case reads s of
    [(x, "")] -> Just x
    _ -> Nothing 

astToStx :: AST -> Either Error Stx 
astToStx tuple = do
    head  <- tuplehd atom tuple
    case head of 
      "\\" -> do 
        ((), x, body) <- tuple3f astignore atom astToStx tuple
        return $ StxLam x body
      "$" -> do 
        ((), f, x) <- tuple3f astignore astToStx astToStx tuple
        return $ StxApp f x
      "if" -> do 
        ((), cond, t, e) <- tuple4f astignore astToStx astToStx astToStx tuple
        return $ StxIf cond t e
      "+" -> do 
        ((), lhs, rhs) <- tuple3f astignore astToStx astToStx tuple
        return $ StxOp Add [lhs, rhs]
      "-" -> do
        ((), lhs, rhs) <- tuple3f astignore astToStx astToStx tuple
        return $ StxOp Sub [lhs, rhs]
      "*" -> do
        ((), lhs, rhs) <- tuple3f astignore astToStx astToStx tuple
        return $ StxOp Mul [lhs, rhs]
      "==" -> do
        ((), lhs, rhs) <- tuple3f astignore astToStx astToStx tuple
        return $ StxOp CondEq [lhs, rhs]
      str -> do 
        case parseIntFromString str of 
          Just i -> pure $ StxConst $ ConstInt i
          Nothing -> 
            case str of 
              "true" -> pure $ StxConst $ ConstBool True
              "false" -> pure $ StxConst $ ConstBool False
              _ -> pure $ StxVar str

-- (decl <name> <rhs>)
astToDecl :: AST -> Either Error Decl 
astToDecl tuple = do
  (_, name, rhs) <- tuple3f (atomString "decl") atom astToStx tuple 
  return $ Decl name rhs

main :: IO ()
main = do
  args <- getArgs
  path <- case args of
           [path] -> pure path
           _ -> (putStrLn "expected single file path to parse") >> exitFailure
  file <- readFile path
  putStrLn $"file contents:"
  putStrLn $ file
  putStrLn $ "parsing..."
  ast <- case AST.parse file of
           Left failure -> putStrLn failure >> exitFailure
           Right success -> pure success
  putStrLn $ astPretty ast
  putStrLn $ "convering to intermediate repr..."
  decls <- case tuplefor astToDecl ast of
            Left failure -> putStrLn failure >> exitFailure
            Right d -> pure d
  let out = foldl (\output decl -> 
          let (eitherValErr, env') = runEvalM (declEval decl) (outputEnv output)  in
          case eitherValErr of 
            Left err -> output { outputErrors = M.insert (declLhs decl) err (outputErrors output) }
            Right val -> output { outputValues = M.insert (declLhs decl) val (outputValues output) }
          ) mempty decls
  print out
