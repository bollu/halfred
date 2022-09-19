#!/usr/bin/env runghc
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
{-# LANGUAGE LambdaCase #-}
import qualified Data.Map.Strict as M
import Control.Monad(ap, forM, (>=>))
import System.Environment
import System.Exit
import Data.List
import AST
import Data.Either
import Control.Monad(foldM)
import GHC.Stack

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

instance Show Const where 
    show (ConstInt i) = show i

data IsDyn where
    S :: IsDyn
    D :: IsDyn

instance Show IsDyn where
    show S = "S"
    show D = "D"

data Stx where 
  StxConst :: Const -> Stx 
  StxLift :: Stx -> Stx
  StxVar :: Var -> Stx 
  StxLam :: IsDyn -> Var -> Stx -> Stx
  StxApp :: IsDyn -> Stx -> Stx -> Stx
  StxIf :: IsDyn -> Stx -> Stx -> Stx -> Stx
  StxFix :: IsDyn -> Stx -> Stx
  StxOp :: IsDyn -> Opcode -> [Stx] -> Stx

instance Show Stx where 
    show (StxConst c) = "(const " ++ show c ++ ")"
    show (StxVar v) = "(var " ++ v ++ ")"
    show (StxLift e) = "(lift " ++ show e ++ ")"
    show (StxFix dyn e) = "(fix " ++ show dyn ++ " " ++ show e ++ ")"
    show (StxLam dyn v e) = "(\\" ++ show dyn ++ " " ++ v ++ " " ++ show e ++ ")"
    show (StxApp dyn e1 e2) = "($" ++ show dyn ++ " " ++ show e1 ++ " " ++ show e2 ++ ")"
    show (StxIf dyn e1 e2 e3) = "(if " ++ show e1 ++ " " ++ show e2 ++ " " ++ show e3 ++ ")"
    show (StxOp dyn op es) = "(op " ++ show op ++ " " ++ show dyn ++ " " ++ intercalate " " (map show es) ++ ")"

-- vvv L1 Evaluator vvv
data Val where
    ValConst :: Const -> Val
    ValFun :: (Val -> EvalM Val)  -- encoding will not work in Lean due to universes
       -> Val

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
eval (StxLam dyn xname body) =
  pure $ ValFun (\xval -> evalInsertEnv xname xval >> eval body)
eval (StxFix dyn e) = eval e >>= \case
  ValFun f -> f (ValFun f) -- this only works in lazy language.
  v -> evalError (ExpectedValConstError v)
eval (StxApp dyn f x) = do
  vf <- eval f
  vx <- eval x
  case vf of
    ValConst c -> evalError (ExpectedValFnError c)
    ValFun f -> f vx
eval (StxIf dyn cond t e) = do
  vcond <- eval cond
  case vcond of
    ValConst (ConstInt i) -> if i /= 0 then eval t else eval e
-- eval (StxOp [] )
eval stx = evalError (UnknownStxError stx)

-- ^^ L1 evaluator ^^


-- vv L2 evaluator vv
data Val2 where
    ValConst2 :: Const -> Val2
    ValFun2 :: (Val2 -> EvalM2 Val2)  -- encoding will not work in Lean due to universes
       -> Val2
    ValCode2 :: Stx -> Val2

instance Show Val2 where 
    show (ValConst2 c) = "<const '" ++ show c ++ "'>"
    show (ValFun2 _) = "<fun>"
    show (ValCode2 c) = "<code '" ++ show c ++ "'>"

  
type EvalEnv2 = M.Map Var Val2
data EvalError2 where 
  UnableToFindVarError2 :: Var -> EvalError2
  ExpectedValFnError2 :: Val2 -> EvalError2
  ExpectedValConstError2 :: Val2 -> EvalError2
  ExpectedValCode2 :: Val2 -> EvalError2
  UnknownStxError2 :: Stx -> EvalError2


instance Show EvalError2 where 
  show (UnableToFindVarError2 v) = "UnableToFindVarError2: " ++ v
  show (ExpectedValFnError2 c) = "ExpectedValFnError2: " ++ show c
  show (ExpectedValConstError2 v) = "ExpectedValConstError2: " ++ show v
  show (ExpectedValCode2 v) = "ExpectedValCodeError2: " ++ show v
  show (UnknownStxError2 s) = "UnknownStxError2: " ++ show s

data EvalM2 a =
  EvalM2 {
    runEvalM2 :: EvalEnv2 -> (Either EvalError2 a, EvalEnv2)
  } deriving(Functor)


evalLookupEnv2 :: HasCallStack => Var -> EvalM2 Val2
evalLookupEnv2 name =
  EvalM2 $ \env ->
    case M.lookup name env of
      Just val -> (Right val, env)
      Nothing -> (Left (UnableToFindVarError2 name), env)

evalInsertEnv2 :: HasCallStack => Var -> Val2 -> EvalM2 ()
evalInsertEnv2 name val =
  EvalM2 $ \env -> (Right (), M.insert name val env)

scopedEnv2 :: HasCallStack => EvalM2 a -> EvalM2 a
scopedEnv2 (EvalM2 f) = EvalM2 $ \env -> let (val, env') = f env in (val, env)

evalError2 :: HasCallStack => EvalError2 -> EvalM2 a
-- evalError2 err = EvalM2 $ \env -> (Left err, env)
evalError2 err = EvalM2 $ \env -> error $ show (err, env)

evalFreshName2 :: HasCallStack => Var -> EvalM2 Var
evalFreshName2 v = pure (v ++ ".f")

val2ToConst2 :: HasCallStack => Val2 -> EvalM2 Const
val2ToConst2 (ValConst2 c) = pure c
val2ToConst2 v = evalError2 $ ExpectedValConstError2 v


val2ToValFun2 :: HasCallStack => Val2 -> EvalM2 (Val2 -> EvalM2 Val2)
val2ToValFun2 (ValFun2 f) = pure f
val2ToValFun2 v = evalError2 $ ExpectedValFnError2 v

val2ToCode2 :: HasCallStack => Val2 -> EvalM2 Stx
val2ToCode2 (ValCode2 c) = pure c
val2ToCode2 v = evalError2 $ ExpectedValCode2 v


instance Monad EvalM2 where
  return a = EvalM2 (\env -> (return a, env))
  ma >>= a2mb =
    EvalM2(\env -> let (ea, env') = runEvalM2 ma env in
             case ea of
             Left e -> (Left e, env')
             Right a -> let mb = a2mb a in runEvalM2 mb env')

instance Applicative EvalM2 where
  pure = return
  (<*>) = ap

eval2 :: HasCallStack => Stx -> EvalM2 Val2
eval2 (StxConst c) = pure (ValConst2 c)
eval2 (StxVar v) = evalLookupEnv2 v
eval2 (StxLam D xname body) =
  pure $ ValFun2 (\xval ->  evalInsertEnv2 xname xval >> eval2 body)
eval2 (StxFix D e) = eval2 e >>= \case
  ValFun2 f -> f (ValFun2 f) -- this only works in lazy language.
  v -> evalError2 (ExpectedValConstError2 v)
eval2 (StxApp D f x) = do
  vf <- eval2 f >>= val2ToValFun2
  vx <- eval2 x
  vf vx

eval2 (StxIf D cond t e) = do
  (ConstInt i) <- eval2 cond >>= val2ToConst2
  if i /= 0 then eval2 t else eval2 e
eval2 (StxOp D Mul [a, b]) = do
  (ConstInt i) <- eval2 a >>= val2ToConst2
  (ConstInt j) <- eval2 b >>= val2ToConst2
  return (ValConst2 (ConstInt $ i*j))
eval2 (StxOp D Sub [a, b]) = do
  (ConstInt i) <- eval2 a >>= val2ToConst2
  (ConstInt j) <- eval2 b >>= val2ToConst2
  return (ValConst2 (ConstInt $ i-j))
eval2 (StxOp D CondEq [a, b]) = do
  (ConstInt i) <- eval2 a >>= val2ToConst2
  (ConstInt j) <- eval2 b >>= val2ToConst2
  return (ValConst2 (ConstInt $ if i == j then 1 else 0))

-- fun rules
eval2 (StxLift stx) = do
  v <- eval2 stx
  case v of
    ValConst2 c -> pure $ ValCode2 (StxConst  c) -- readback!
    _ ->  evalError2 (ExpectedValConstError2 v)
eval2 (StxLam S xname body) = do -- readback!
    xname' <- evalFreshName2 xname
    -- body' <- scopedEnv2 $ do  
    body' <- do 
       evalInsertEnv2 xname (ValCode2 (StxVar xname'))
       eval2 body
    body' <- val2ToCode2 body'
    return  $ ValCode2 (StxLam D xname' body')
eval2 (StxApp S f x) = do -- readback!
    cf <- eval2 f >>= val2ToCode2
    cx <- eval2 x >>= val2ToCode2
    return  $ ValCode2 (StxApp D cf cx)
eval2 (StxFix S f) = do -- readback!
    cf <- eval2 f >>= val2ToCode2  -- will this actually terminate? o_O I do have a monad! I might have to rewrite this using applicative..?
    return $ ValCode2 (StxFix D cf)
eval2 (StxIf S cond t e) = do -- readback!
    ccond <- eval2 cond >>= val2ToCode2
    ct <- eval2 t >>= val2ToCode2
    ce <- eval2 e >>= val2ToCode2
    return $ ValCode2 (StxIf D ccond ct ce)
eval2 (StxOp S op args) = do -- readback!
    cargs <- forM args (eval2 >=> val2ToCode2)
    return $ ValCode2 (StxOp D op cargs)
eval2 stx = evalError2 (UnknownStxError2 stx)

-- ^^ L2 evaluator ^^

-- vv Declarations, parsing, etc. -- 

data Decl = Decl {
  declLhs :: String,
  declRhs :: Stx
}

-- declEval :: Decl -> EvalM Val
-- declEval decl = do
--   v <- eval (declRhs decl) -- evaluate
--   evalInsertEnv (declLhs decl) v -- add to env
--   return v -- return to toplevel


declEval2 :: HasCallStack => Decl -> EvalM2 Val2
declEval2 decl = do
  v <- eval2 (declRhs decl) -- evaluate
  evalInsertEnv2 (declLhs decl) v -- add to env
  return v -- return to toplevel

-- | Output of running a program.
data Output = Output { 
    outputErrors :: M.Map String EvalError2
    , outputValues :: M.Map String Val2
    , outputEnv :: EvalEnv2
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
        "Errors: " ++ show (M.toList errs) ++
        "\nOutputs:\n  " ++ intercalate "\n  " (map show $ M.toList vals) ++
        "\nEnvironment:\n  " ++ intercalate "\n  " (map show $ M.toList env)
        
  
parseIntFromString :: String -> Maybe Int
parseIntFromString s = 
  case reads s of
    [(x, "")] -> Just x
    _ -> Nothing 


astToIsDyn :: AST -> Either Error IsDyn
astToIsDyn ast = atom ast >>= \case
    "S" -> pure S
    "D" -> pure D 
    tag -> Left $ errAtSpan (astspan ast) $ "unknown Dyn tag '" ++ show tag ++ "'"


astToStx :: AST -> Either Error Stx 
astToStx a@(Atom span str) = 
    case parseIntFromString str of 
      Just i -> pure $ StxConst $ ConstInt i
      Nothing -> 
        case str of 
          "true" -> pure $ StxConst $ ConstInt 1
          "false" -> pure $ StxConst $ ConstInt 0
          _ -> pure $ StxVar str
astToStx tuple = do
    head  <- tuplehd atom tuple
    case head of 
      "\\" -> do 
        ((), dyn, x, body) <- tuple4f astignore astToIsDyn atom astToStx tuple
        return $ StxLam dyn x body
      "$" -> do 
        ((), dyn, f, x) <- tuple4f astignore astToIsDyn astToStx astToStx tuple
        return $ StxApp dyn f x
      "fix" -> do 
        ((), dyn, e) <- tuple3f astignore astToIsDyn astToStx tuple
        return $ StxFix dyn e
      "lift" -> do 
        ((), e) <- tuple2f astignore astToStx tuple
        return $ StxLift e
      "comptime" -> do 
        ((), e) <- tuple2f astignore astToStx tuple
        return $ StxLift e
      "if" -> do 
        ((), dyn, cond, t, e) <- tuple5f astignore astToIsDyn astToStx astToStx astToStx tuple
        return $ StxIf dyn cond t e
      "+" -> do 
        ((), dyn, lhs, rhs) <- tuple4f astignore astToIsDyn astToStx astToStx tuple
        return $ StxOp dyn Add [lhs, rhs]
      "-" -> do
        ((), dyn, lhs, rhs) <- tuple4f astignore astToIsDyn astToStx astToStx tuple
        return $ StxOp dyn Sub [lhs, rhs]
      "*" -> do
        ((), dyn, lhs, rhs) <- tuple4f astignore astToIsDyn astToStx astToStx tuple
        return $ StxOp dyn Mul [lhs, rhs]
      "==" -> do
        ((), dyn, lhs, rhs) <- tuple4f astignore astToIsDyn astToStx astToStx tuple
        return $ StxOp dyn CondEq [lhs, rhs]
      _ -> Left $ errAtSpan (astspan tuple) $ "Unexpected tuple head: " ++ show head

-- (decl <name> <rhs>)
astToDecl :: AST -> Either Error [Decl]
astToDecl tuple = do
  head  <- tuplehd atom tuple
  case head of
    "decl" -> do 
      (_, name, rhs) <- tuple3f (atomString "decl") atom astToStx tuple 
      return $ [Decl name rhs]
    "--" -> return []
    _ -> Left $ errAtSpan (astspan tuple) $ "Unexpected head, expected '--' or 'decl'. Unexpected: " ++ show head


-- TODO: Type system to derive static/dynamic annotations

main :: HasCallStack => IO ()
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
  decls <- case tuplefor' astToDecl ast of
            Left failure -> putStrLn failure >> exitFailure
            Right d -> pure d
  let out = foldl (\output decl -> 
          let (eitherValErr, env') = runEvalM2 (declEval2 decl) (outputEnv output)  in
          case eitherValErr of 
            Left err -> output { outputErrors = M.insert (declLhs decl) err (outputErrors output), outputEnv = env' }
            Right val -> output { outputValues = M.insert (declLhs decl) val (outputValues output), outputEnv = env' }
          ) mempty decls
  print out

