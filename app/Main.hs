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
import Data.Text.Prettyprint.Doc ((<+>))
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Text.Megaparsec as P
import qualified Data.ByteString.Char8 as BS
import Data.Singletons
import Lab.Untyped
import Lab.LLVM
import Lab.Types
import Lab.AST
import Lab.Errors
import Lab.Decls
import Lab.Monad
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
import System.Console.Haskeline

main :: IO ()
main = runInputT defaultSettings $
  runLab repl >>= \case
  Left err -> renderPretty $ prettyError err
  Right _ -> pure ()

repl :: Lab ()
repl = prompt "> " >>= \case
  Nothing -> pure ()
  Just input -> do
    untypedAST <- parse (pack input)
    typecheck untypedAST $ \sty ast -> do
      renderPretty $ PP.pretty ("Expression parsed successfully with type" :: String) <+> PP.pretty ("::" :: String) <+> PP.pretty sty
      loop untypedAST sty ast
  where loop uast sty ast = prompt "> " >>= \case
          Just "untyped" -> renderString uast >> loop uast sty ast
          Just "typed"   -> printAST sty ast >> loop uast sty ast
          Just "eval"    -> evalAST ast >> loop uast sty ast
          Just "pretty"  -> renderPretty (prettyAST ast) >> loop uast sty ast
          -- Just "llvm"    -> genLLVM sty ast >> loop uast sty ast
          -- Just "jit"     -> runJit sty ast >> loop uast sty ast
          -- Just "compile" -> genASM sty ast >> loop uast sty ast
          Just "quit"    -> quit
          Just _         -> liftIO (putStrLn "invalid command") >> loop uast sty ast
          Nothing        -> pure ()

parse :: MonadError LabError m => Text -> m Untyped
parse = either (throwError . ParseError . P.errorBundlePretty) pure . P.parse (parseLanguage <* P.eof) ""

printAST :: MonadIO m => Sing ty -> AST '[] ty -> m ()
printAST sty ast =
  renderPretty $ PP.pretty (show ast) <+> PP.pretty ("::" :: String) <+> PP.pretty sty

-- genLLVM :: MonadIO m => SLType ty -> AST '[] ty -> m ()
-- genLLVM ty = liftIO . TL.putStrLn . PP.ppllvm . wrapper ty

evalAST :: MonadIO m => AST '[] ty -> m ()
evalAST = renderPretty . prettyAST . Lab.Eval.expr . eval

-- jit :: Context -> (EE.MCJIT -> IO a) -> IO a
-- jit c = EE.withMCJIT c (Just 0) Nothing Nothing Nothing

-- runJit :: MonadIO m => SLType ty -> AST '[] ty -> m ()
-- runJit ty ast = liftIO $
--   withContext $ \context ->
--   withModuleFromAST context (wrapper ty ast) $ \mod ->
--   withPassManager defaultPassSetSpec $ \pm -> do
--     verify mod
--     s <- moduleLLVMAssembly mod
--     BS.putStrLn s
--     jit context $ \executionEngine ->
--       EE.withModuleInEngine executionEngine mod $ \ee ->
--       EE.getFunction ee (AST.Name "f") >>= \case
--         Just fn -> case ty of
--           SLInt -> callFFI fn retInt [] >>= print
--           SLBool -> fmap (/= 0) (callFFI fn retInt []) >>= print
--           SLUnit -> callFFI fn retVoid []
--           _ -> error "Not implemented yet"
--         Nothing -> putStrLn "Error?"
-- 
-- genASM :: MonadIO m => SLType ty -> AST '[] ty -> m ()
-- genASM ty ast = liftIO $
--   withContext $ \context ->
--   withModuleFromAST context (wrapper ty ast) $ \mod ->
--   withPassManager defaultPassSetSpec $ \pm -> do
--     verify mod
--     s <- moduleLLVMAssembly mod
--     BS.putStrLn s
--     withHostTargetMachineDefault $ \tm -> do
--       gen <- moduleTargetAssembly tm mod
--       BS.putStrLn gen
