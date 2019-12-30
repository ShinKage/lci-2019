{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Foreign.Ptr
import Foreign.Storable.Tuple ()
import Foreign.LibFFI
import Foreign.LibFFI.Base
import Foreign.LibFFI.FFITypes
import Foreign.LibFFI.Internal
import Foreign.Storable
import Data.Text
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
          Just "step"    -> stepAST ast >> loop uast sty ast
          Just "pretty"  -> renderPretty (prettyAST ast) >> loop uast sty ast
          Just "llvm"    -> genLLVM sty ast >> loop uast sty ast
          Just "jit"     -> runJit sty ast >> loop uast sty ast
          Just "compile" -> genASM sty ast >> loop uast sty ast
          Just "quit"    -> quit
          Just _         -> liftIO (putStrLn "invalid command") >> loop uast sty ast
          Nothing        -> pure ()

parse :: MonadError LabError m => Text -> m Untyped
parse = either (throwError . ParseError . P.errorBundlePretty) pure . P.parse (parseLanguage <* P.eof) ""

printAST :: MonadIO m => Sing ty -> AST '[] ty -> m ()
printAST sty ast =
  renderPretty $ PP.pretty (show ast) <+> PP.pretty ("::" :: String) <+> PP.pretty sty

genLLVM :: (MonadError LabError m, MonadFix m, MonadIO m) => SLType ty -> AST '[] ty -> m ()
genLLVM ty ast = do
  m <- wrapper ty $ buildEnv ast
  liftIO . TL.putStrLn . PP.ppllvm $ m

evalAST :: MonadIO m => AST '[] ty -> m ()
evalAST = renderPretty . prettyAST . Lab.Eval.expr . eval

stepAST :: MonadIO m => AST '[] ty -> m ()
stepAST = renderPretty . PP.vsep . fmap prettyStep . stepDescent
  where stepDescent :: AST '[] ty -> [Step ty]
        stepDescent e = StepAST e : case step e of
          StepAST e' -> stepDescent e'
          StepValue e' -> [StepAST $ Lab.Eval.expr e']

jit :: Context -> (EE.MCJIT -> IO a) -> IO a
jit c = EE.withMCJIT c (Just 0) Nothing Nothing Nothing

runJit :: (MonadError LabError m, MonadFix m, MonadIO m) => SLType ty -> AST '[] ty -> m ()
runJit ty ast = do
  m <- wrapper ty $ buildEnv ast
  liftIO $ withContext $ \context ->
    withModuleFromAST context m $ \m' ->
    withPassManager defaultPassSetSpec $ \_ -> do
      verify m'
      s <- moduleLLVMAssembly m'
      BS.putStrLn s
      jit context $ \executionEngine ->
        EE.withModuleInEngine executionEngine m' $ \ee ->
        EE.getFunction ee (AST.Name "expr") >>= \case
          Just fn -> ffiRet ty $ \(_, retty, free) -> do
            c <- callFFI fn retty []
            print c
            free
          Nothing -> putStrLn "Error?"

-- FIXME: Nested pairs
ffiRet :: SLType ty -> (forall t. (Show t, Storable t) => (Ptr CType, RetType t, IO ()) -> IO r) -> IO r
ffiRet SLInt k = k (ffi_type_hs_int, retInt, pure ())
ffiRet SLBool k = k (ffi_type_hs_int, mkStorableRetType ffi_type_hs_int :: RetType Bool, pure ())
ffiRet SLUnit k = k (ffi_type_pointer, mkStorableRetType ffi_type_pointer :: RetType (), pure ())
ffiRet (SLProduct a b) k =
  ffiRet a $ \(r1, _ :: RetType a, f1) ->
  ffiRet b $ \(r2, _ :: RetType b, f2) -> do
    (r, f) <- newStructCType [r1, r2]
    k (r, mkStorableRetType r :: RetType (a, b), f1 >> f2 >> f)
ffiRet _ _ = error "Not a value"

genASM :: (MonadError LabError m, MonadFix m, MonadIO m) => SLType ty -> AST '[] ty -> m ()
genASM ty ast = do
  m <- wrapper ty $ buildEnv ast
  liftIO $ withContext $ \context ->
    withModuleFromAST context m $ \m' ->
    withPassManager defaultPassSetSpec $ \_ -> do
      verify m'
      s <- moduleLLVMAssembly m'
      BS.putStrLn s
      withHostTargetMachineDefault $ \tm -> do
        gen <- moduleTargetAssembly tm m'
        BS.putStrLn gen
