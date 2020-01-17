{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}

-------------------------------------------------------------------------------
-- |
-- Module      : Lab.Untyped
-- Description : Untyped version of the Lab AST, used for parsing.
-- Copyright   : (c) Giuseppe Lomurno, 2019
-- License     : ...
-- Maintainer  : Giuseppe Lomurno <g.lomurno@studenti.unipi.it>
-- Stability   : experimental
-- Portability : non-portable (?)
--
-------------------------------------------------------------------------------

module Lab.Untyped where

import Control.Monad.Except
import Data.Kind
import Data.List (elemIndex)
import Data.List.Extra
import Data.Singletons.Decide
import Data.Singletons.Prelude hiding (Elem)
import Data.Singletons.Sigma
import Data.Text

import Lab.AST
import Lab.Errors (LabError)
import qualified Lab.Errors as Err
import Lab.Types

type Name = Text

-- | Untyped Abstract Syntax Tree used for parsing.
data Untyped :: Type where
  -- | An integer literal.
  UIntE :: Integer -> Untyped
  -- | A boolean literal.
  UBoolE :: Bool -> Untyped
  -- | Unit literal.
  UUnitE :: Untyped
  -- | Primitive unary operators.
  UPrimUnaryOp :: UnaryOp arg ret -> Untyped -> Untyped
  -- | Primitive binary operators.
  UPrimBinaryOp :: BinaryOp arg1 arg2 ret -> Untyped -> Untyped -> Untyped
  -- | Conditional expressions.
  UCond :: Untyped -> Untyped -> Untyped -> Untyped
  -- | Lambda abstraction with explicit argument type.
  ULambda :: Name -> SomeSing LType -> Untyped -> Untyped
  -- | Named variable.
  UVar :: Name -> Untyped
  -- | Lambda application.
  UApp :: Untyped -> Untyped -> Untyped
  -- | Pair of expressions.
  UPair :: Untyped -> Untyped -> Untyped
  -- | Fixpoint operator for recursive functions support.
  UFix :: Untyped -> Untyped
  -- | Pure IO value.
  UIOPure :: Untyped -> Untyped
  -- | Impure IO function.
  UIOBind :: Untyped -> Untyped -> Untyped
  -- | Impure IO, reads a limited set of value from the stdin.
  UIOPrimRead :: SomeSing LType -> Untyped

deriving instance Show Untyped

instance Eq Untyped where
  (UIntE n) == (UIntE n') = n == n'
  (UBoolE b) == (UBoolE b') = b == b'
  UUnitE == UUnitE = True
  (UPrimUnaryOp op e) == (UPrimUnaryOp op' e') = op `eqUnary` op' && e == e'
  (UPrimBinaryOp op e1 e2) == (UPrimBinaryOp op' e1' e2') = op `eqBinary` op' && e1 == e1' && e2 == e2'
  (UCond c e1 e2) == (UCond c' e1' e2') = c == c' && e1 == e1' && e2 == e2'
  (ULambda n ty e) == (ULambda n' ty' e') = n == n' && ty == ty' && e == e'
  (UVar n) == (UVar n') = n == n'
  (UApp e1 e2) == (UApp e1' e2') = e1 == e1' && e2 == e2'
  (UPair e1 e2) == (UPair e1' e2') = e1 == e1' && e2 == e2'
  (UFix e) == (UFix e') = e == e'
  (UIOPure e) == (UIOPure e') = e == e'
  (UIOBind e1 e2) == (UIOBind e1' e2') = e1 == e1' && e2 == e2'
  (UIOPrimRead ty) == (UIOPrimRead ty') = ty == ty'
  _ == _ = False

-- | Typechecks an untyped AST. Produces a well-formed typed AST in CPS style.
-- The continuation is required to avoid complex type definition and
-- existential types to return the dependently typed AST.
typecheck :: MonadError LabError m
          => Untyped
          -> (forall ty. Sing ty -> AST '[] ty -> m r)
          -> m r
typecheck = go SNil []
  where
    go :: MonadError LabError m
       => Sing env
       -> [Name]
       -> Untyped
       -> (forall ty. Sing ty -> AST env ty -> m r)
       -> m r
    go _ _ (UIntE n) k = k sing (IntE n)
    go _ _ (UBoolE b) k = k sing (BoolE b)
    go _ _ UUnitE k = k sing UnitE

    go env names (UCond c e1 e2) k =
      go env names c $ \tyc' c' -> case tyc' %~ SLBool of -- Check must be a boolean
        Disproved _ -> throwError $ Err.expectedType SLBool tyc' "Cond requires a boolean guard"
        Proved Refl ->
          go env names e1 $ \ty1' e1' ->
          go env names e2 $ \ty2' e2' -> case ty1' %~ ty2' of -- Both branches must be of the same type
            Proved Refl -> k ty2' (Cond c' e1' e2')
            Disproved _ -> throwError $ Err.typeMismatch ty1' ty2' "Cond requires two branches of the same type"

    go env names (UVar name) k = case elemIndex name names >>= maybeElem env of
      Just (ty :&: prf) -> k ty (Var prf)
      Nothing -> throwError $ Err.undefReference (unpack name)

    go env names (ULambda name (SomeSing argTy) body) k =
      go (SCons argTy env) (name : names) body $ \retTy body' ->
        k (SLArrow argTy retTy) (Lambda argTy body')

    go env names (UApp lam arg) k =
      go env names lam $ \lamTy body ->
      go env names arg $ \argTy arg' -> case lamTy of
        SLArrow argTy' retTy -> case argTy' %~ argTy of -- Argument type must match the required type
          Proved Refl -> k retTy (App body arg')
          Disproved _ -> throwError $ Err.expectedType argTy argTy' "Application requires an argument of the declared type"
        _ -> throwError $ Err.lambdaRequired lamTy "Application requires a lambda abstraction"

    go env names (UFix lam) k =
      go env names lam $ \lamTy body -> case lamTy of
        SLArrow argTy retTy -> case argTy %~ retTy of -- Fixpoint requires a lambda with matching argument and return type
          Proved Refl -> k retTy (Fix body)
          Disproved _ -> throwError $ Err.expectedType retTy argTy "Fixpoint operator requires a lambda with same argument and return type"
        _ -> throwError $ Err.lambdaRequired lamTy "Fixpoint operator requires a lambda abstraction"

    go env names (UPair l r) k =
      go env names l $ \lTy l' ->
      go env names r $ \rTy r' ->
        k (SLProduct lTy rTy) (Pair l' r')

    go env names (UIOPure e) k =
      go env names e $ \ty e' ->
        k (SLIO ty) (IOPure e')

    go env names (UIOBind x f) k =
      go env names x $ \xTy x' ->
      go env names f $ \fTy f' -> case fTy of
        SLArrow argTy (SLIO retTy) -> case xTy of
          SLIO pty -> case argTy %~ pty of
            Proved Refl -> k (SLIO retTy) (IOBind x' f')
            Disproved _ -> throwError $ Err.expectedType argTy pty "IO Bind operation requires that the type inside the monad and the lambda are the same"
          _ -> throwError $ Err.ioValueError xTy "IO Bind operation requires a monadic value"
        _ -> throwError $ Err.lambdaRequired fTy "IO Bind operation requires a monadic lambda abstraction"

    go _ _ (UIOPrimRead (SomeSing t)) k = case t of
      SLInt -> k (SLIO t) (IOPrimRead t)
      SLBool -> k (SLIO t) (IOPrimRead t)
      SLUnit -> k (SLIO t) (IOPrimRead t)
      _ -> throwError $ Err.ioUnsupportedRead t "IO read supports a limited subset of types"

    go env names (UPrimUnaryOp PrimNot e) k =
      go env names e $ \ty' e' -> case ty' %~ SLBool of
        Proved Refl -> k sing (PrimUnaryOp PrimNot e')
        Disproved _ -> throwError $ Err.expectedType SLBool ty' "Not operator requires a boolean"
    go env names (UPrimUnaryOp PrimNeg e) k =
      go env names e $ \ty' e' -> case ty' %~ SLInt of
        Proved Refl -> k sing (PrimUnaryOp PrimNeg e')
        Disproved _ -> throwError $ Err.expectedType SLInt ty' "Neg operator requires an integer"
    go env names (UPrimUnaryOp PrimFst e) k =
      go env names e $ \ty' e' -> case ty' of
        SLProduct lTy _ -> k lTy (PrimUnaryOp PrimFst e')
        _ -> throwError $ Err.pairRequired ty' "Fst operator requires a pair"
    go env names (UPrimUnaryOp PrimSnd e) k =
      go env names e $ \ty' e' -> case ty' of
        SLProduct _ rTy -> k rTy (PrimUnaryOp PrimSnd e')
        _ -> throwError $ Err.pairRequired ty' "Snd operator requires a pair"

    go env names (UPrimBinaryOp PrimAdd e1 e2) k =
      go env names e1 $ \ty1' e1' -> case ty1' %~ SLInt of
        Disproved _ -> throwError $ Err.expectedType SLInt ty1' "Add operator requires integers"
        Proved Refl ->
          go env names e2 $ \ty2' e2' -> case ty2' %~ SLInt of
            Proved Refl -> k sing (PrimBinaryOp PrimAdd e1' e2')
            Disproved _ -> throwError $ Err.expectedType SLInt ty2' "Add operator requires two integers"
    go env names (UPrimBinaryOp PrimSub e1 e2) k =
      go env names e1 $ \ty1' e1' -> case ty1' %~ SLInt of
        Disproved _ -> throwError $ Err.expectedType SLInt ty1' "Sub operator requires two integers"
        Proved Refl ->
          go env names e2 $ \ty2' e2' -> case ty2' %~ SLInt of
            Proved Refl -> k sing (PrimBinaryOp PrimSub e1' e2')
            Disproved _ -> throwError $ Err.expectedType SLInt ty2' "Sub operator requires two integers"
    go env names (UPrimBinaryOp PrimMul e1 e2) k =
      go env names e1 $ \ty1' e1' -> case ty1' %~ SLInt of
        Disproved _ -> throwError $ Err.expectedType SLInt ty1' "Mul operator requires two integers"
        Proved Refl ->
          go env names e2 $ \ty2' e2' -> case ty2' %~ SLInt of
            Proved Refl -> k sing (PrimBinaryOp PrimMul e1' e2')
            Disproved _ -> throwError $ Err.expectedType SLInt ty2' "Mul operator requires two integers"
    go env names (UPrimBinaryOp PrimDiv e1 e2) k =
      go env names e1 $ \ty1' e1' -> case ty1' %~ SLInt of
        Disproved _ -> throwError $ Err.expectedType SLInt ty1' "Div operator requires two integers"
        Proved Refl ->
          go env names e2 $ \ty2' e2' -> case ty2' %~ SLInt of
            Proved Refl -> k sing (PrimBinaryOp PrimDiv e1' e2')
            Disproved _ -> throwError $ Err.expectedType SLInt ty1' "Div operator requires two integers"
    go env names (UPrimBinaryOp PrimAnd e1 e2) k =
      go env names e1 $ \ty1' e1' -> case ty1' %~ SLBool of
        Disproved _ -> throwError $ Err.expectedType SLBool ty1' "And operator requires two booleans"
        Proved Refl ->
          go env names e2 $ \ty2' e2' -> case ty2' %~ SLBool of
            Proved Refl -> k sing (PrimBinaryOp PrimAnd e1' e2')
            Disproved _ -> throwError $ Err.expectedType SLBool ty2' "And operator requires two booleans"
    go env names (UPrimBinaryOp PrimOr e1 e2) k =
      go env names e1 $ \ty1' e1' -> case ty1' %~ SLBool of
        Disproved _ -> throwError $ Err.expectedType SLBool ty1' "Or operator requires two boolean"
        Proved Refl ->
          go env names e2 $ \ty2' e2' -> case ty2' %~ SLBool of
            Proved Refl -> k sing (PrimBinaryOp PrimOr e1' e2')
            Disproved _ -> throwError $ Err.expectedType SLBool ty2' "Or operator requires two integers"
    go env names (UPrimBinaryOp PrimLT e1 e2) k =
      go env names e1 $ \ty1' e1' -> case ty1' %~ SLInt of
        Disproved _ -> throwError $ Err.expectedType SLInt ty1' "Less than operator requires two integers"
        Proved Refl ->
          go env names e2 $ \ty2' e2' -> case ty2' %~ SLInt of
            Proved Refl -> k sing (PrimBinaryOp PrimLT e1' e2')
            Disproved _ -> throwError $ Err.expectedType SLInt ty2' "Less than operator requires two integers"
    go env names (UPrimBinaryOp PrimGT e1 e2) k =
      go env names e1 $ \ty1' e1' -> case ty1' %~ SLInt of
        Disproved _ -> throwError $ Err.expectedType SLInt ty1' "Greater than operator requires two integers"
        Proved Refl ->
          go env names e2 $ \ty2' e2' -> case ty2' %~ SLInt of
            Proved Refl -> k sing (PrimBinaryOp PrimGT e1' e2')
            Disproved _ -> throwError $ Err.expectedType SLInt ty2' "Greater than operator requires two integers"
    go env names (UPrimBinaryOp PrimLE e1 e2) k =
      go env names e1 $ \ty1' e1' -> case ty1' %~ SLInt of
        Disproved _ -> throwError $ Err.expectedType SLInt ty1' "Less or equal than operator requires two integers"
        Proved Refl ->
          go env names e2 $ \ty2' e2' -> case ty2' %~ SLInt of
            Proved Refl -> k sing (PrimBinaryOp PrimLE e1' e2')
            Disproved _ -> throwError $ Err.expectedType SLInt ty2' "Less or equal than operator requires two integers"
    go env names (UPrimBinaryOp PrimGE e1 e2) k =
      go env names e1 $ \ty1' e1' -> case ty1' %~ SLInt of
        Disproved _ -> throwError $ Err.expectedType SLInt ty1' "Greater or equal than operator requires two integers"
        Proved Refl ->
          go env names e2 $ \ty2' e2' -> case ty2' %~ SLInt of
            Proved Refl -> k sing (PrimBinaryOp PrimGE e1' e2')
            Disproved _ -> throwError $ Err.expectedType SLInt ty2' "Greater or equal than operator requires two integers"
    go env names (UPrimBinaryOp PrimEq e1 e2) k =
      go env names e1 $ \ty1' e1' ->
      go env names e2 $ \ty2' e2' -> case ty1' %~ ty2' of
        Proved Refl -> k sing (PrimBinaryOp PrimEq e1' e2')
        Disproved _ -> throwError $ Err.typeMismatch ty1' ty2' "Equal operator requires two parameters of equal type"
    go env names (UPrimBinaryOp PrimNeq e1 e2) k =
      go env names e1 $ \ty1' e1' ->
      go env names e2 $ \ty2' e2' -> case ty1' %~ ty2' of
        Proved Refl -> k sing (PrimBinaryOp PrimNeq e1' e2')
        Disproved _ -> throwError $ Err.typeMismatch ty1' ty2' "Not equal operator requires two parameters of equal type"
