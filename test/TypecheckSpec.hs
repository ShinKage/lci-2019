{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeInType #-}

module TypecheckSpec where

import Control.Monad.Except
import Data.Either
import Data.List.Extra
import Data.Singletons
import Test.Hspec

import Lab.AST
import Lab.Types
import Lab.Untyped

typecheckSpec :: Spec
typecheckSpec =
  describe "typecheck" $ do
    it "checks trivial constructors" $ do
      runExcept (typecheck (UIntE 42) $ \ty e -> case (ty, e) of
        (SLInt, IntE 42) -> pure True
        _ -> pure False) `shouldBe` Right True
      runExcept (typecheck (UBoolE True) $ \ty e -> case (ty, e) of
        (SLBool, BoolE True) -> pure True
        _ -> pure False) `shouldBe` Right True
      runExcept (typecheck UUnitE $ \ty e -> case (ty, e) of
        (SLUnit, UnitE) -> pure True
        _ -> pure False) `shouldBe` Right True
    it "checks operator parameters type" $ do
      runExcept (typecheck (UPrimUnaryOp PrimNeg (UIntE 42)) $ \ty e -> case (ty, e) of
        (SLInt, PrimUnaryOp PrimNeg (IntE 42)) -> pure True
        _ -> pure False) `shouldBe` Right True
      runExcept (typecheck (UPrimUnaryOp PrimNeg (UBoolE True)) $ \_ _ -> pure True) `shouldSatisfy` isLeft
      runExcept (typecheck (UPrimBinaryOp PrimLE (UIntE 42) (UIntE 42)) $ \ty e -> case (ty, e) of
        (SLBool, PrimBinaryOp PrimLE (IntE 42) (IntE 42)) -> pure True
        _ -> pure False) `shouldBe` Right True
      runExcept (typecheck (UPrimBinaryOp PrimLE (UBoolE True) (UIntE 42)) $ \_ _ -> pure True) `shouldSatisfy` isLeft
      runExcept (typecheck (UPrimBinaryOp PrimEq (UIntE 42) (UIntE 42)) $ \ty e -> case (ty, e) of
        (SLBool, PrimBinaryOp PrimEq (IntE 42) (IntE 42)) -> pure True
        _ -> pure False) `shouldBe` Right True
      runExcept (typecheck (UPrimBinaryOp PrimEq UUnitE UUnitE) $ \ty e -> case (ty, e) of
        (SLBool, PrimBinaryOp PrimEq UnitE UnitE) -> pure True
        _ -> pure False) `shouldBe` Right True
    it "checks pair construction" $
      runExcept (typecheck (UPair (UIntE 42) UUnitE) $ \ty e -> case (ty, e) of
        (SLProduct SLInt SLUnit, Pair (IntE 42) UnitE) -> pure True
        _ -> pure False) `shouldBe` Right True
    it "checks condition branch" $ do
      runExcept (typecheck (UCond (UBoolE True) (UIntE 2) (UIntE 1)) $ \ty e -> case (ty, e) of
        (SLInt, Cond (BoolE True) (IntE 2) (IntE 1)) -> pure True
        _ -> pure False) `shouldBe` Right True
      runExcept (typecheck (UCond (UBoolE True) (UIntE 42) (UBoolE True)) $ \_ _ -> pure True) `shouldSatisfy` isLeft
      runExcept (typecheck (UCond UUnitE (UBoolE True) (UBoolE False)) $ \_ _ -> pure True) `shouldSatisfy` isLeft
    it "checks lambda abstraction" $ do
      runExcept (typecheck (ULambda "x" (toSing LInt) (UVar "x")) $ \ty e -> case (ty, e) of
        (SLArrow SLInt SLInt, Lambda SLInt (Var Here)) -> pure True
        _ -> pure False) `shouldBe` Right True
      runExcept (typecheck (ULambda "x" (toSing LInt) (ULambda "y" (toSing LInt) (UPrimBinaryOp PrimAdd (UVar "x") (UVar "y")))) $ \ty e -> case (ty, e) of
        (SLArrow SLInt (SLArrow SLInt SLInt), Lambda SLInt (Lambda SLInt (PrimBinaryOp PrimAdd (Var (There Here)) (Var Here)))) -> pure True
        _ -> pure False) `shouldBe` Right True
      runExcept (typecheck (ULambda "x" (toSing LInt) (UBoolE True)) $ \ty e -> case (ty, e) of
        (SLArrow SLInt SLBool, Lambda SLInt (BoolE True)) -> pure True
        _ -> pure False) `shouldBe` Right True
      runExcept (typecheck (ULambda "x" (toSing LInt) (UVar "y")) $ \_ _ -> pure True) `shouldSatisfy` isLeft
      runExcept (typecheck (UApp (ULambda "x" (toSing LInt) (UPrimBinaryOp PrimLT (UVar "x") (UIntE 3))) (UIntE 5)) $ \ty e -> case (ty, e) of
        (SLBool, App (Lambda SLInt (PrimBinaryOp PrimLT (Var Here) (IntE 3))) (IntE 5)) -> pure True
        _ -> pure False) `shouldBe` Right True
      runExcept (typecheck (UApp (ULambda "x" (toSing LBool) (UVar "x")) UUnitE) $ \_ _ -> pure True) `shouldSatisfy` isLeft
    it "checks fixpoint operator" $ do
      runExcept (typecheck (UFix (ULambda "f" (toSing (LArrow LInt LInt)) (ULambda "x" (toSing LInt) (UApp (UVar "f") (UVar "x"))))) $ \ty e -> case (ty, e) of
        (SLArrow SLInt SLInt, Fix (Lambda (SLArrow SLInt SLInt) (Lambda SLInt (App (Var (There Here)) (Var Here))))) -> pure True
        _ -> pure False) `shouldBe` Right True
      runExcept (typecheck (UFix UUnitE) $ \_ _ -> pure True) `shouldSatisfy` isLeft
