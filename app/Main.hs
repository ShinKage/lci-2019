{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import           Control.Monad.Except
import qualified Data.ByteString.Char8 as BS
import           Data.Singletons
import           Data.Text
import qualified Data.Text.Lazy.IO as TL
import           Data.Text.Prettyprint.Doc
import qualified Text.Megaparsec as P

import qualified Foreign.LibFFI as FFI
import qualified Foreign.LibFFI.Base as FFI
import qualified Foreign.LibFFI.FFITypes as FFI
import qualified Foreign.LibFFI.Internal as FFI (CType)
import qualified Foreign.Storable as FFI
import qualified Foreign.Storable.Tuple ()
import qualified Foreign.Ptr as FFI

import qualified LLVM.Pretty as PP
import qualified LLVM.AST as LLVM
import           LLVM.Context as LLVM
import           LLVM.Module as LLVM
import           LLVM.PassManager as LLVM
import           LLVM.Analysis as LLVM
import           LLVM.Target as LLVM
import qualified LLVM.ExecutionEngine as LLVM

import System.Console.Haskeline

import Lab

main :: IO ()
main = runInputT defaultSettings $
  runLab repl >>= \case
    Left err -> renderPretty $ prettyError err
    Right _  -> pure ()

repl :: Lab ()
repl = prompt "> " >>= \case
  Nothing -> pure ()
  Just input -> do
    untypedAST <- parse $ pack input
    typecheck untypedAST $ \sty tast -> do
      renderPretty $ pretty ("Expression parsed successfully with type" :: String) <+> colon <> colon <+> pretty sty
      loop untypedAST sty tast
  where loop uast sty tast = prompt "> " >>= \case
          Just "untyped" -> printUntyped uast >> loop uast sty tast
          Just "typed"   -> printAST sty tast >> loop uast sty tast
          Just "eval"    -> evalAST tast >> loop uast sty tast
          Just "step"    -> stepAST tast >> loop uast sty tast
          Just "pretty"  -> renderPretty (prettyAST tast) >> loop uast sty tast
          Just "codegen" -> genIR sty tast >> loop uast sty tast
          Just "llvm"    -> genLLVM sty tast >> loop uast sty tast
          Just "jit"     -> runJit sty tast >> loop uast sty tast
          Just "compile" -> genASM sty tast >> loop uast sty tast
          Just "quit"    -> quit
          Just _         -> liftIO (putStrLn "invalid command") >> loop uast sty tast
          Nothing        -> pure ()

parse :: MonadError LabError m => Text -> m Untyped
parse = either (throwError . parseError . P.errorBundlePretty) pure . P.parse (parseLanguage <* P.eof) ""

printAST :: MonadIO m => Sing ty -> AST '[] ty -> m ()
printAST sty tast = renderPretty $ pretty (show tast) <+> colon <> colon <+> pretty sty

printUntyped :: MonadIO m => Untyped -> m ()
printUntyped = renderString

genIR :: (MonadError LabError m, MonadFix m, MonadIO m) => SLType ty -> AST '[] ty -> m ()
genIR _ tast = do
  let Env { expr=e, decl=ds } = buildEnv tast
  renderPretty $ pretty ("Top-Level declarations:" :: String)
  renderPretty . vsep . fmap prettyDecl $ ds
  renderPretty $ pretty ("Body:" :: String)
  renderPretty . prettyCodegenAST $ e
    where prettyDecl (Decl {argsType=as, body=b}) =
            hcat (punctuate comma (fmap pretty as))
              <+> colon
              <+> prettyCodegenAST b

genLLVM :: (MonadError LabError m, MonadFix m, MonadIO m) => SLType ty -> AST '[] ty -> m ()
genLLVM ty tast = do
  m <- wrapper ty $ buildEnv tast
  liftIO . TL.putStrLn . PP.ppllvm $ m

evalAST :: MonadIO m => AST '[] ty -> m ()
evalAST = renderPretty . prettyAST . ast . eval

stepAST :: MonadIO m => AST '[] ty -> m ()
stepAST = renderPretty . vsep . fmap prettyStep . stepDescent
  where stepDescent :: AST '[] ty -> [Step ty]
        stepDescent e = StepAST e : case step e of
          StepAST e' -> stepDescent e'
          StepValue e' -> [StepAST $ ast e']

jit :: Context -> (LLVM.MCJIT -> IO a) -> IO a
jit c = LLVM.withMCJIT c (Just 0) Nothing Nothing Nothing

runJit :: (MonadError LabError m, MonadFix m, MonadIO m) => SLType ty -> AST '[] ty -> m ()
runJit ty tast = do
  m <- wrapper ty $ buildEnv tast
  liftIO $ withContext $ \context ->
    withModuleFromAST context m $ \m' ->
    withPassManager defaultPassSetSpec $ \_ -> do
      verify m'
      s <- moduleLLVMAssembly m'
      BS.putStrLn s
      jit context $ \executionEngine ->
        LLVM.withModuleInEngine executionEngine m' $ \ee ->
        LLVM.getFunction ee (LLVM.Name "expr") >>= \case
          Just fn -> ffiRet ty $ \(_, retty, free) -> do
            c <- FFI.callFFI fn retty []
            print c
            free
          Nothing -> putStrLn "Error?"

-- FIXME: Nested pairs
ffiRet :: SLType ty -> (forall t. (Show t, FFI.Storable t) => (FFI.Ptr FFI.CType, FFI.RetType t, IO ()) -> IO r) -> IO r
ffiRet SLInt k = k (FFI.ffi_type_hs_int, FFI.retInt, pure ())
ffiRet SLBool k = k (FFI.ffi_type_hs_int, FFI.mkStorableRetType FFI.ffi_type_uint8 :: FFI.RetType Bool, pure ())
ffiRet SLUnit k = k (FFI.ffi_type_pointer, FFI.mkStorableRetType FFI.ffi_type_pointer :: FFI.RetType (), pure ())
ffiRet (SLProduct a b) k =
  ffiRet a $ \(r1, _ :: FFI.RetType a, f1) ->
  ffiRet b $ \(r2, _ :: FFI.RetType b, f2) -> do
    (r, f) <- FFI.newStructCType [r1, r2]
    k (r, FFI.mkStorableRetType r :: FFI.RetType (a, b), f1 >> f2 >> f)
ffiRet _ _ = error "Not a value"

genASM :: (MonadError LabError m, MonadFix m, MonadIO m) => SLType ty -> AST '[] ty -> m ()
genASM ty tast = do
  m <- wrapper ty $ buildEnv tast
  liftIO $ withContext $ \context ->
    withModuleFromAST context m $ \m' ->
    withPassManager defaultPassSetSpec $ \_ -> do
      verify m'
      s <- moduleLLVMAssembly m'
      BS.putStrLn s
      withHostTargetMachineDefault $ \tm -> do
        gen <- moduleTargetAssembly tm m'
        BS.putStrLn gen
