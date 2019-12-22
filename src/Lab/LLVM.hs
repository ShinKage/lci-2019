{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
import Data.String
import Control.Monad.State
import Control.Monad.Except
import Data.Singletons
import LLVM.AST (Module)
import LLVM.AST.Constant as LLVM
import LLVM.AST.Name as LLVM
import LLVM.AST.Operand (Operand(..))
import LLVM.AST.IntegerPredicate as LLVM
import LLVM.AST.Type as LLVM
import LLVM.AST.Typed as LLVM
import LLVM.IRBuilder as LLVM

import Lab.Decls
import Lab.Types
import Lab.Errors

data EnvState = EnvState { decls :: [Operand]
                         , args :: [Operand]
                         , lastFun :: Int
                         }

emptyEnvState :: EnvState
emptyEnvState = EnvState [] [] 0

-- | Wraps the generated code in a single function.
wrapper :: (MonadFix m, MonadError LabError m) => SLType ty -> CodegenEnv -> m Module
wrapper ty cenv = buildModuleT "exe" $ flip runStateT emptyEnvState $ do
  decls' <- topLevelFunctions (decl cenv)
  function "expr" [] (labToLLVM $ fromSing ty) $ \[] -> mdo
    _ <- block `named` "entry"
    modify $ \env -> env { decls = decls' }
    e' <- codegen (expr cenv)
    ret e'
    -- case ty %~ SLUnit of
    --   Proved Refl -> retVoid
    --   Disproved _ -> LLVM.ret e'

labToLLVM :: LType -> Type
labToLLVM LInt  = i32
labToLLVM LBool = i1
labToLLVM LUnit = ptr i8
labToLLVM (LProduct a b) = StructureType False [labToLLVM a, labToLLVM b]
labToLLVM (LArrow _ _) = error "Expression must return a value"
labToLLVM LVoid = error "Void cannot be instantiated"

topLevelFunctions :: (MonadState EnvState m, MonadError LabError m, MonadFix m, MonadModuleBuilder m)
                  => [Declaration]
                  -> m [Operand]
topLevelFunctions decls' = forM decls' $ \dec -> do
    let argTypes = getArgTypes (argsType dec)
    name <- getFunName
    function name argTypes (labToLLVM $ retType dec) $ \args' -> mdo
      modify $ \env -> env { args = reverse args' }
      _ <- block `named` "entry"
      body' <- codegen (body dec)
      modify $ \env -> env { args = [] }
      ret body'

  where argName :: Int -> ParameterName
        argName i = fromString $ "arg_" ++ show i

        getFunName :: MonadState EnvState m => m Name
        getFunName = do i <- gets lastFun
                        let name = fromString $ "fun_" ++ show i
                        modify $ \env -> env { lastFun = i + 1 }
                        pure name

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
codegen (CLambda _ _ _)          = throwError (CodegenError "Lambda not lifted")
codegen app@(CApp _ _) = do
  let (f, as) = viewApp app
  f' <- codegen f
  args' <- traverse (fmap (, []) . codegen) as
  call f' args'
codegen (CCall i) = do
  ds <- gets decls
  case index' i ds of
    Just d -> pure d
    Nothing -> throwError (CodegenError "Function index out of range")

-- CApp (CApp (CCall 0) (CIntE 42)) (CIntE 69)
-- Decl {argsType = [LInt], retType = LArrow LInt LInt, body = CCall 1}
-- Decl {argsType = [LInt], retType = LInt, body = CPrimUnaryOp PrimNeg (CVar 0)}

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
  case index' i ds of
    Just d  -> call d params'
    Nothing -> throwError $ CodegenError "Function index out of range"

litInt :: MonadIRBuilder m => Integer -> m Operand
litInt n = pure $ int32 n

litBool :: MonadIRBuilder m => Bool -> m Operand
litBool b = pure $ bit $ if b then 1 else 0

litUnit :: MonadIRBuilder m => m Operand
litUnit = pure $ ConstantOperand (Null (ptr i8))

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
  ifElse <- block `named` "if.else"
  e2' <- codegen e2
  br ifExit
  ifExit <- block `named` "if.exit"
  phi [(e1', ifThen), (e2', ifElse)]


unaryOp :: (MonadState EnvState m, MonadError LabError m, MonadFix m, MonadIRBuilder m)
        => UnaryOp arg ret
        -> CodegenAST
        -> m Operand
unaryOp op e = do
  e' <- codegen e
  case op of
    PrimNeg -> sub (int32 0) e'
    PrimNot -> xor e' (bit 0x1)
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

index' :: Int -> [a] -> Maybe a
index' _ [] = Nothing
index' i (x : xs) | i < 0     = Nothing
                  | i == 0    = Just x
                  | otherwise = index' (i - 1) xs
