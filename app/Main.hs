{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Foreign.LibFFI
import Data.Text
import qualified Data.Text.IO as T
import qualified Data.Text.Lazy.IO as TL
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Text.Megaparsec as P
import qualified Data.ByteString.Char8 as BS
import Data.Singletons
import Lab.Untyped
import Lab.LLVM
import Lab.Types
import Lab.AST
import Lab.Eval
import Lab.Parser (parseLanguage)
import qualified LLVM.Pretty as PP
import qualified LLVM.AST as AST
import LLVM.Context
import LLVM.Module
import LLVM.PassManager
import LLVM.Analysis
import LLVM.Target
import qualified LLVM.ExecutionEngine as EE
import Control.Monad.Except

main :: IO ()
main = runExceptT repl >>= \case
  Left err -> putStrLn err
  Right _ -> pure ()

repl :: (MonadIO m, MonadError String m) => m ()
repl = do
  input <- liftIO T.getLine
  untypedAST <- parse input
  liftIO $ print untypedAST
  typecheck untypedAST $ \sty ast -> do
    printAST sty ast
    cmd <- liftIO T.getLine
    case cmd of
      "llvm"    -> genLLVM sty ast
      "eval"    -> evalAST ast
      "pretty"  -> liftIO $ print $ PP.pretty ast
      "jit"     -> runJit sty ast
      "compile" -> genASM sty ast
      _         -> liftIO $ putStrLn "invalid command"

parse :: MonadError String m => Text -> m Untyped
parse = either (throwError . P.errorBundlePretty) pure . P.parse (parseLanguage <* P.eof) ""

printAST :: MonadIO m => Sing ty -> AST '[] ty -> m ()
printAST sty ast =
  liftIO $ print $ PP.pretty (show ast) PP.<+> PP.pretty ("::" :: String) PP.<+> PP.pretty sty

genLLVM :: MonadIO m => SLType ty -> AST '[] ty -> m ()
genLLVM ty = liftIO . TL.putStrLn . PP.ppllvm . wrapper ty

evalAST :: MonadIO m => AST '[] ty -> m ()
evalAST = liftIO . print . PP.pretty . expr . eval

jit :: Context -> (EE.MCJIT -> IO a) -> IO a
jit c = EE.withMCJIT c (Just 0) Nothing Nothing Nothing

runJit :: MonadIO m => SLType ty -> AST '[] ty -> m ()
runJit ty ast = liftIO $
  withContext $ \context ->
  withModuleFromAST context (wrapper ty ast) $ \mod ->
  withPassManager defaultPassSetSpec $ \pm -> do
    verify mod
    s <- moduleLLVMAssembly mod
    BS.putStrLn s
    jit context $ \executionEngine ->
      EE.withModuleInEngine executionEngine mod $ \ee ->
      EE.getFunction ee (AST.Name "f") >>= \case
        Just fn -> case ty of
          SLInt -> callFFI fn retInt [] >>= print
          SLBool -> fmap (/= 0) (callFFI fn retInt []) >>= print
          SLUnit -> callFFI fn retVoid []
          _ -> error "Not implemented yet"
        Nothing -> putStrLn "Error?"

genASM :: MonadIO m => SLType ty -> AST '[] ty -> m ()
genASM ty ast = liftIO $
  withContext $ \context ->
  withModuleFromAST context (wrapper ty ast) $ \mod ->
  withPassManager defaultPassSetSpec $ \pm -> do
    verify mod
    s <- moduleLLVMAssembly mod
    BS.putStrLn s
    withHostTargetMachineDefault $ \tm -> do
      gen <- moduleTargetAssembly tm mod
      BS.putStrLn gen
