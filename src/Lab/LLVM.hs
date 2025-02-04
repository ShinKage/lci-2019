{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeInType #-}

-------------------------------------------------------------------------------
-- |
-- Module      : Lab.LLVM
-- Description : Code generation for LLVM IR.
-- Copyright   : (c) Giuseppe Lomurno, 2019
-- License     : ...
-- Maintainer  : Giuseppe Lomurno <g.lomurno@studenti.unipi.it>
-- Stability   : experimental
-- Portability : non-portable (?)
--
-------------------------------------------------------------------------------

module Lab.LLVM where

import Prelude hiding (EQ, and, or)

import           Control.Monad.Except
import           Control.Monad.State
import           Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import           Data.Singletons
import           Data.String
import           LLVM.AST (Module)
import qualified LLVM.AST as AST
import qualified LLVM.AST.CallingConvention as CC
import           LLVM.AST.Constant as LLVM
import           LLVM.AST.IntegerPredicate as LLVM
import           LLVM.AST.Operand (Operand(..))
import           LLVM.AST.Type as LLVM
import           LLVM.AST.Typed as LLVM
import           LLVM.IRBuilder as LLVM

import           Lab.Decls
import           Lab.Errors
import           Lab.Types

data EnvState = EnvState { decls :: Map Int Operand
                         , args :: [Operand]
                         , lets :: [LazyLet]
                         , lastFunOperand :: Maybe Operand
                         , lastFunRet :: AST.Type
                         }

data LazyLet = LazyLet { evaluated :: Operand
                       , valLoc :: Operand
                       , code :: CodegenAST
                       }

emptyEnvState :: EnvState
emptyEnvState = EnvState Map.empty [] [] Nothing LLVM.void

-- | Wraps the generated code in a single function with lifted lambdas.
wrapper :: (MonadFix m, MonadError LabError m) => SLType ty -> CodegenEnv -> m Module
wrapper ty cenv = buildModuleT "exe" $ flip runStateT emptyEnvState $ do
  topLevelFunctions (decl cenv)
  function "lab_main" [] (labToLLVM $ fromSing ty) $ \[] -> mdo
    _ <- block `named` "entry"
    e' <- codegen $ expr cenv
    ret e'

-- | Generate the code for lifted lambda abstractions.
topLevelFunctions :: (MonadState EnvState m, MonadError LabError m, MonadFix m, MonadModuleBuilder m)
                  => Map Int Declaration
                  -> m ()
topLevelFunctions decls' = forM_ (Map.toDescList decls') $ \(idx, dec) -> mdo
    let argTypes = getArgTypes (argsType dec)
    let retty = labToLLVM $ retType dec
    let name = fromString $ "fun_" ++ show idx
    f <- function name argTypes retty $ \args' -> do
      modify $ \env -> env { args = reverse args', lastFunOperand = Just f, lastFunRet = retty, lets = [] }
      _ <- block `named` "entry"
      body' <- codegen (body dec)
      modify $ \env -> env { args = [], lastFunOperand = Nothing, lastFunRet = LLVM.void, lets = [] }
      ret body'
    ds' <- gets decls
    modify $ \env -> env { decls = Map.insert idx f ds' }
    pure f
  where argName :: Int -> ParameterName
        argName i = fromString $ "arg_" ++ show i

        getArgTypes :: [LType] -> [(Type, ParameterName)]
        getArgTypes = zipWith (\i arg -> (labToLLVM arg, argName i)) [0..]

-- | LLVM IR generation for the typed AST.
codegen :: (MonadState EnvState m, MonadError LabError m, MonadFix m, MonadIRBuilder m)
        => CodegenAST
        -> m Operand
codegen (CIntE n)                = litInt n
codegen (CBoolE n)               = litBool n
codegen CUnitE                   = litUnit
codegen (CPrimUnaryOp op e)      = unaryOp op e
codegen (CPrimBinaryOp op e1 e2) = binaryOp op e1 e2
codegen (CCond c e1 e2)          = conditional c e1 e2
codegen (CVar i)                 = varBinding i
codegen (CPair f s)              = pairStruct f s
codegen (CLambda _ _ _)          = throwError $ CodegenError "Lambda not lifted"
codegen (CFix _)                 = throwError $ CodegenError "Fix not lifted"
codegen app@(CApp _ _)           = appImpl app
codegen (CCall i)                = callImpl i
codegen CRecToken                = recToken
codegen (CLet e1 e2)             = letImpl e1 e2
codegen (CLetRef i)              = letRef i

recToken :: (MonadState EnvState m, MonadError LabError m, MonadFix m, MonadIRBuilder m)
         => m Operand
recToken = gets lastFunOperand >>= \case
  Just f -> pure f
  Nothing -> throwError $ CodegenError "Token can be only placed in recursive functions"

appImpl :: (MonadState EnvState m, MonadError LabError m, MonadFix m, MonadIRBuilder m)
        => CodegenAST
        -> m Operand
appImpl app = do
  let (f, as) = viewApp app
  f' <- codegen f
  args' <- traverse (fmap (, []) . codegen) as
  retty <- gets lastFunRet
  -- call f' args'
  let instr = AST.Call {
    AST.tailCallKind = Nothing
  , AST.callingConvention = CC.C
  , AST.returnAttributes = []
  , AST.function = Right f'
  , AST.arguments = args'
  , AST.functionAttributes = []
  , AST.metadata = []
  }
  emitInstr retty instr

callImpl :: (MonadState EnvState m, MonadError LabError m, MonadFix m, MonadIRBuilder m)
         => Int
         -> m Operand
callImpl i = do
  ds <- gets decls
  case Map.lookup i ds of
           Just d -> pure d
           Nothing -> throwError (CodegenError "Function index out of range")

letImpl :: (MonadState EnvState m, MonadError LabError m, MonadFix m, MonadIRBuilder m)
        => CodegenAST
        -> CodegenAST
        -> m Operand
letImpl e1 e2 = do
  evloc <- alloca i1 (Just $ bit 0) 0x0
  (vty, _) <- runIRBuilderT emptyIRBuilder $ typeOf <$> codegen e1
  valloc <- alloca vty Nothing 0x0
  let ll = LazyLet evloc valloc e1
  old <- gets lets
  modify $ \env -> env { lets = old ++ [ll] }
  codegen e2

letRef :: (MonadState EnvState m, MonadError LabError m, MonadFix m, MonadIRBuilder m)
       => Int
       -> m Operand
letRef i = index' i <$> gets lets >>= \case
  Just ll -> mdo
    ev <- load (evaluated ll) 0x0
    condBr ev ifThen ifElse
    ifThen <- block `named` "let.ev"
    e1' <- load (valLoc ll) 0x0
    br ifExit
    thenBlock <- currentBlock
    ifElse <- block `named` "let.notev"
    e2' <- codegen (code ll)
    store (valLoc ll) 0x0 e2'
    store (evaluated ll) 0x0 (bit 1)
    br ifExit
    elseBlock <- currentBlock
    ifExit <- block `named` "let.exit"
    phi [(e1', thenBlock), (e2', elseBlock)]
  Nothing -> throwError $ CodegenError "Let index out of range"

viewApp :: CodegenAST -> (CodegenAST, [CodegenAST])
viewApp = go []
  where
    go xs (CApp a b) = go (b : xs) a
    go xs f = (f, xs)

varBinding :: (MonadState EnvState m, MonadError LabError m, MonadIRBuilder m)
           => Int
           -> m Operand
varBinding i = do
  args' <- gets args
  case index' i args' of
    Just arg -> pure arg
    Nothing  -> throwError $ CodegenError "Variable index out of range"

funCall :: (MonadState EnvState m, MonadError LabError m, MonadFix m, MonadIRBuilder m)
        => Int
        -> [CodegenAST]
        -> m Operand
funCall i params = do
  ds <- gets decls
  params' <- traverse (fmap (, []) . codegen) params
  case Map.lookup i ds of
    Just d  -> call d params'
    Nothing -> throwError $ CodegenError "Function index out of range"

litInt :: MonadIRBuilder m => Integer -> m Operand
litInt = pure . int32

litBool :: MonadIRBuilder m => Bool -> m Operand
litBool b = pure . bit $ if b then 1 else 0

litUnit :: MonadIRBuilder m => m Operand
litUnit = pure . ConstantOperand . Null $ ptr i8

pairStruct :: (MonadState EnvState m, MonadError LabError m, MonadFix m, MonadIRBuilder m)
           => CodegenAST
           -> CodegenAST
           -> m Operand
pairStruct f s = do
  f' <- codegen f
  s' <- codegen s
  let agg = struct Nothing False [Undef (typeOf f'), Undef (typeOf s')]
  onlyFirst <- insertValue agg f' [0]
  insertValue onlyFirst s' [1]

conditional :: (MonadState EnvState m, MonadError LabError m, MonadFix m, MonadIRBuilder m)
            => CodegenAST
            -> CodegenAST
            -> CodegenAST
            -> m Operand
conditional c e1 e2 = mdo
  c' <- codegen c
  condBr c' ifThen ifElse
  ifThen <- block `named` "if.then"
  e1' <- codegen e1
  br ifExit
  thenBlock <- currentBlock
  ifElse <- block `named` "if.else"
  e2' <- codegen e2
  br ifExit
  elseBlock <- currentBlock
  ifExit <- block `named` "if.exit"
  phi [(e1', thenBlock), (e2', elseBlock)]

unaryOp :: (MonadState EnvState m, MonadError LabError m, MonadFix m, MonadIRBuilder m)
        => UnaryOp arg ret
        -> CodegenAST
        -> m Operand
unaryOp op e = do
  e' <- codegen e
  case op of
    PrimNeg -> sub (int32 0) e'
    PrimNot -> xor e' (bit 0x1) -- X XOR 1 <=> NOT X
    PrimFst -> extractValue e' [0]
    PrimSnd -> extractValue e' [1]

binaryOp :: (MonadState EnvState m, MonadError LabError m, MonadFix m, MonadIRBuilder m)
         => BinaryOp arg1 arg2 ret
         -> CodegenAST
         -> CodegenAST
         -> m Operand
binaryOp op e1 e2 = do
  e1' <- codegen e1
  e2' <- codegen e2
  case op of
    PrimAdd -> add e1' e2'
    PrimSub -> sub e1' e2'
    PrimMul -> mul e1' e2'
    PrimDiv -> sdiv e1' e2'
    PrimLT  -> icmp SLT e1' e2'
    PrimGT  -> icmp SGT e1' e2'
    PrimLE  -> icmp SLE e1' e2'
    PrimGE  -> icmp SGE e1' e2'
    PrimEq  -> icmp EQ e1' e2'
    PrimNeq -> icmp NE e1' e2'
    PrimAnd -> and e1' e2'
    PrimOr  -> or e1' e2'

-- | Converts Lab types to the corresponding LLVM types.
labToLLVM :: LType -> Type
labToLLVM LInt  = i32
labToLLVM LBool = i1
labToLLVM LUnit = ptr i8
labToLLVM (LProduct a b) = StructureType False [labToLLVM a, labToLLVM b]
labToLLVM (LArrow a b) = ptr $ FunctionType (labToLLVM b) [labToLLVM a] False
labToLLVM LVoid = error "Void cannot be instantiated"

index' :: Int -> [a] -> Maybe a
index' _ [] = Nothing
index' i (x : xs) | i < 0     = Nothing
                  | i == 0    = Just x
                  | otherwise = index' (i - 1) xs
