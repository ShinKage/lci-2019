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
import Data.Text
import Data.Kind
import Data.List.Extra
import Data.List (elemIndex)
import Data.Singletons.Prelude hiding (Elem)
import Data.Singletons.Decide
import Data.Singletons.Sigma

import Lab.AST
import Lab.Types

type Name = Text

-- | Untyped Abstract Syntax Tree used for parsing.
data Untyped :: Type where
  UIntE :: Integer -> Untyped
  UBoolE :: Bool -> Untyped
  UUnitE :: Untyped
  UPrimUnaryOp :: UnaryOp arg ret -> Untyped -> Untyped
  UPrimBinaryOp :: BinaryOp arg1 arg2 ret -> Untyped -> Untyped -> Untyped
  UCond :: Untyped -> Untyped -> Untyped -> Untyped
  ULambda :: Name -> SomeSing LType -> Untyped -> Untyped
  UVar :: Name -> Untyped
  UApp :: Untyped -> Untyped -> Untyped
  UPair :: Untyped -> Untyped -> Untyped
  UFix :: Untyped -> Untyped

deriving instance Show Untyped

-- | Typechecks an untyped AST. Produces a well-formed typed AST in CPS style.
-- The continuation is required to avoid complex type definition and
-- existential types to return the dependently typed AST.
typecheck :: MonadError String m -- TODO: Use custom error type
          => Untyped
          -> (forall ty. Sing ty -> AST '[] ty -> m r)
          -> m r
typecheck = go SNil []
  where
    go :: MonadError String m
       => Sing env
       -> [Name]
       -> Untyped
       -> (forall ty. Sing ty -> AST env ty -> m r) -> m r
    go _ _ (UIntE n) k = k sing (IntE n)
    go _ _ (UBoolE b) k = k sing (BoolE b)
    go _ _ UUnitE k = k sing UnitE

    go env names (UCond c e1 e2) k =
      go env names c $ \tyc' c' ->
      go env names e1 $ \ty1' e1' ->
      go env names e2 $ \ty2' e2' -> case (tyc' %~ SLBool, ty1' %~ ty2') of
        (Proved Refl, Proved Refl) -> k ty2' (Cond c' e1' e2')
        (_, _) -> throwError "Cond requires a boolean guard and two branches of the same type"

    go env names (UVar name) k = case elemIndex name names >>= maybeElem env of
      Just (ty :&: prf) -> k ty (Var prf)
      Nothing -> throwError "Var references an undefined name"

    go env names (ULambda name (SomeSing argTy) body) k =
      go (SCons argTy env) (name : names) body $ \retTy body' ->
        k (SLArrow argTy retTy) (Lambda argTy body')

    go env names (UApp lam arg) k =
      go env names lam $ \lamTy body ->
      go env names arg $ \argTy arg' -> case lamTy of
        SLArrow argTy' retTy -> case argTy' %~ argTy of
          Proved Refl -> k retTy (App body arg')
          Disproved _ -> throwError "Application requires an argument of the declared type"
        _ -> throwError "Application requires a lambda abstraction"

    go env names (UFix lam) k =
      go env names lam $ \lamTy body -> case lamTy of
        SLArrow argTy retTy -> case argTy %~ retTy of
          Proved Refl -> k retTy (Fix body)
          _ -> throwError "Fixpoint operator requires a lambda with same argument and return type"
        _ -> throwError "Fixpoint operator requires a lambda abstraction"

    go env names (UPair l r) k =
      go env names l $ \lTy l' ->
      go env names r $ \rTy r' ->
        k (SLProduct lTy rTy) (Pair l' r')

    go env names (UPrimUnaryOp PrimNot e) k =
      go env names e $ \ty' e' -> case ty' %~ SLBool of
        Proved Refl -> k sing (PrimUnaryOp PrimNot e')
        Disproved _ -> throwError "Not operator requires a boolean"
    go env names (UPrimUnaryOp PrimNeg e) k =
      go env names e $ \ty' e' -> case ty' %~ SLInt of
        Proved Refl -> k sing (PrimUnaryOp PrimNeg e')
        Disproved _ -> throwError "Neg operator requires an integer"
    go env names (UPrimUnaryOp PrimFst e) k =
      go env names e $ \ty' e' -> case ty' of
        SLProduct lTy _ -> k lTy (PrimUnaryOp PrimFst e')
        _ -> throwError "Fst operator requires a pair"
    go env names (UPrimUnaryOp PrimSnd e) k =
      go env names e $ \ty' e' -> case ty' of
        SLProduct _ rTy -> k rTy (PrimUnaryOp PrimSnd e')
        _ -> throwError "Snd operator requires a pair"

    go env names (UPrimBinaryOp PrimAdd e1 e2) k =
      go env names e1 $ \ty1' e1' ->
      go env names e2 $ \ty2' e2' -> case (ty1' %~ SLInt, ty2' %~ SLInt) of
        (Proved Refl, Proved Refl) -> k sing (PrimBinaryOp PrimAdd e1' e2')
        (_, _) -> throwError "Add operator requires two integers"
    go env names (UPrimBinaryOp PrimSub e1 e2) k =
      go env names e1 $ \ty1' e1' ->
      go env names e2 $ \ty2' e2' -> case (ty1' %~ SLInt, ty2' %~ SLInt) of
        (Proved Refl, Proved Refl) -> k sing (PrimBinaryOp PrimSub e1' e2')
        (_, _) -> throwError "Sub operator requires two integers"
    go env names (UPrimBinaryOp PrimMul e1 e2) k =
      go env names e1 $ \ty1' e1' ->
      go env names e2 $ \ty2' e2' -> case (ty1' %~ SLInt, ty2' %~ SLInt) of
        (Proved Refl, Proved Refl) -> k sing (PrimBinaryOp PrimMul e1' e2')
        (_, _) -> throwError "Mul operator requires two integers"
    go env names (UPrimBinaryOp PrimDiv e1 e2) k =
      go env names e1 $ \ty1' e1' ->
      go env names e2 $ \ty2' e2' -> case (ty1' %~ SLInt, ty2' %~ SLInt) of
        (Proved Refl, Proved Refl) -> k sing (PrimBinaryOp PrimDiv e1' e2')
        (_, _) -> throwError "Div operator requires two integers"
    go env names (UPrimBinaryOp PrimAnd e1 e2) k =
      go env names e1 $ \ty1' e1' ->
      go env names e2 $ \ty2' e2' -> case (ty1' %~ SLBool, ty2' %~ SLBool) of
        (Proved Refl, Proved Refl) -> k sing (PrimBinaryOp PrimAnd e1' e2')
        (_, _) -> throwError "And operator requires two integers"
    go env names (UPrimBinaryOp PrimOr e1 e2) k =
      go env names e1 $ \ty1' e1' ->
      go env names e2 $ \ty2' e2' -> case (ty1' %~ SLBool, ty2' %~ SLBool) of
        (Proved Refl, Proved Refl) -> k sing (PrimBinaryOp PrimOr e1' e2')
        (_, _) -> throwError "Or operator requires two integers"
    go env names (UPrimBinaryOp PrimLT e1 e2) k =
      go env names e1 $ \ty1' e1' ->
      go env names e2 $ \ty2' e2' -> case (ty1' %~ SLInt, ty2' %~ SLInt) of
        (Proved Refl, Proved Refl) -> k sing (PrimBinaryOp PrimLT e1' e2')
        (_, _) -> throwError "Less than operator requires two integers"
    go env names (UPrimBinaryOp PrimGT e1 e2) k =
      go env names e1 $ \ty1' e1' ->
      go env names e2 $ \ty2' e2' -> case (ty1' %~ SLInt, ty2' %~ SLInt) of
        (Proved Refl, Proved Refl) -> k sing (PrimBinaryOp PrimGT e1' e2')
        (_, _) -> throwError "Greater than operator requires two integers"
    go env names (UPrimBinaryOp PrimLE e1 e2) k =
      go env names e1 $ \ty1' e1' ->
      go env names e2 $ \ty2' e2' -> case (ty1' %~ SLInt, ty2' %~ SLInt) of
        (Proved Refl, Proved Refl) -> k sing (PrimBinaryOp PrimLE e1' e2')
        (_, _) -> throwError "Less or equal than operator requires two integers"
    go env names (UPrimBinaryOp PrimGE e1 e2) k =
      go env names e1 $ \ty1' e1' ->
      go env names e2 $ \ty2' e2' -> case (ty1' %~ SLInt, ty2' %~ SLInt) of
        (Proved Refl, Proved Refl) -> k sing (PrimBinaryOp PrimGE e1' e2')
        (_, _) -> throwError "Greater or equal than operator requires two integers"
    go env names (UPrimBinaryOp PrimEq e1 e2) k =
      go env names e1 $ \ty1' e1' ->
      go env names e2 $ \ty2' e2' -> case ty1' %~ ty2' of
        Proved Refl -> k sing (PrimBinaryOp PrimEq e1' e2')
        Disproved _ -> throwError "Equal operator requires two integers"
    go env names (UPrimBinaryOp PrimNeq e1 e2) k =
      go env names e1 $ \ty1' e1' ->
      go env names e2 $ \ty2' e2' -> case ty1' %~ ty2' of
        Proved Refl -> k sing (PrimBinaryOp PrimNeq e1' e2')
        Disproved _ -> throwError "Not equal operator requires two integers"
