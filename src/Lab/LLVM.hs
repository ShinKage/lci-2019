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

module Lab.LLVM (wrapper, codegen) where

import Prelude hiding (EQ, and, or)
import Control.Monad.Fix
import Data.Singletons
import Data.Singletons.Decide
import LLVM.AST (Module)
import LLVM.AST.Constant as LLVM
import LLVM.AST.Operand (Operand)
import LLVM.AST.IntegerPredicate as LLVM
import LLVM.AST.Type as LLVM
import LLVM.AST.Typed as LLVM
import LLVM.IRBuilder as LLVM

import Lab.AST
import Lab.Types

-- FIXME: Upgrade to ExceptT transformer

-- | Wraps the generated code in a single function.
wrapper :: SLType ty -> AST env ty -> Module
wrapper ty e = buildModule "exe" $ mdo
  function "f" [] (labToLLVM $ fromSing ty) $ \[] -> mdo
    _ <- block `named` "entry"; do
      e' <- codegen e
      case ty %~ SLUnit of
         Proved Refl -> retVoid
         Disproved _ -> ret e'

labToLLVM :: LType -> Type
labToLLVM LInt  = i32
labToLLVM LBool = i1
labToLLVM LUnit = void
labToLLVM (LProduct a b) = StructureType False [labToLLVM a, labToLLVM b]
labToLLVM (LArrow _ _) = error "Lambda abstraction is currently not supported"
labToLLVM LVoid = error "Void cannot be instantiated"

-- | LLVM IR generation for the typed AST.
codegen :: (MonadFix m, MonadIRBuilder m) => AST env ty -> m Operand
codegen (IntE n) = litInt n
codegen (BoolE n) = litBool n
codegen UnitE = litUnit
codegen (PrimUnaryOp op e) = unaryOp op e
codegen (PrimBinaryOp op e1 e2) = binaryOp op e1 e2
codegen (Cond c e1 e2) = conditional c e1 e2
codegen (Var _) = error "Lambda abstraction is currently not supported"
codegen (Lambda _ _) = error "Lambda abstraction is currently not supported"
codegen (App _ _) = error "Lambda abstraction is currently not supported"
codegen (Fix _) = error "Lambda abstraction is currently not supported"
codegen (Pair f s) = pairStruct f s

litInt :: MonadIRBuilder m => Integer -> m Operand
litInt n = pure $ int32 n

litBool :: MonadIRBuilder m => Bool -> m Operand
litBool b = pure $ bit (if b then 1 else 0)

litUnit :: MonadIRBuilder m => m Operand
litUnit = litBool True

pairStruct :: (MonadFix m, MonadIRBuilder m) => AST env a -> AST env b -> m Operand
pairStruct f s = do
  f' <- codegen f
  s' <- codegen s
  let agg = struct Nothing False [Undef (typeOf f'), Undef (typeOf s')] 
  onlyFirst <- insertValue agg f' [0]
  insertValue onlyFirst s' [1]

conditional :: (MonadFix m, MonadIRBuilder m) => AST env LBool -> AST env ret -> AST env ret -> m Operand
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
  

unaryOp :: (MonadFix m, MonadIRBuilder m) => UnaryOp arg ret -> AST env arg -> m Operand
unaryOp op e = do
  e' <- codegen e
  case op of
    PrimNeg -> sub (int32 0) e'
    PrimNot -> xor e' (bit 0x1)
    PrimFst -> extractValue e' [0]
    PrimSnd -> extractValue e' [1]

binaryOp :: (MonadFix m, MonadIRBuilder m) => BinaryOp arg1 arg2 ret -> AST env arg1 -> AST env arg2 -> m Operand
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
