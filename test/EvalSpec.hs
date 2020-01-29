module EvalSpec where

import Data.List.Extra
import Test.Hspec
import Test.QuickCheck

import Lab.AST
import Lab.Eval
import Lab.Types

evalSpec :: Spec
evalSpec =
  describe "evaluation" $ do
    it "evaluate integers" $ property $
      \x -> val (eval (IntE x)) `shouldBe` (x :: Integer)
    it "evaluate booleans" $ property $
      \x -> val (eval (BoolE x)) `shouldBe` (x :: Bool)
    it "evaluate units" $ val (eval UnitE) `shouldBe` ()
    it "evaluate pairs" $ val (eval $ Pair UnitE (IntE 42)) `shouldBe` ((), 42)
    it "evaluate primitive operations" $ do
      val (eval $ PrimUnaryOp PrimNot (BoolE True)) `shouldBe` False
      val (eval $ PrimUnaryOp PrimNeg (IntE 42)) `shouldBe` (-42)
      val (eval $ PrimUnaryOp PrimFst (Pair UnitE (IntE 42))) `shouldBe` ()
      val (eval $ PrimUnaryOp PrimSnd (Pair UnitE (IntE 42))) `shouldBe` 42
      val (eval $ PrimBinaryOp PrimAdd (IntE 1) (IntE 2)) `shouldBe` 3
      val (eval $ PrimBinaryOp PrimSub (IntE 1) (IntE 2)) `shouldBe` -1
      val (eval $ PrimBinaryOp PrimMul (IntE 1) (IntE 2)) `shouldBe` 2
      val (eval $ PrimBinaryOp PrimDiv (IntE 1) (IntE 2)) `shouldBe` 0
      val (eval $ PrimBinaryOp PrimLE (IntE 1) (IntE 2)) `shouldBe` True
      val (eval $ PrimBinaryOp PrimGE (IntE 1) (IntE 2)) `shouldBe` False
      val (eval $ PrimBinaryOp PrimLT (IntE 1) (IntE 2)) `shouldBe` True
      val (eval $ PrimBinaryOp PrimGT (IntE 1) (IntE 2)) `shouldBe` False
      val (eval $ PrimBinaryOp PrimEq (IntE 1) (IntE 2)) `shouldBe` False
      val (eval $ PrimBinaryOp PrimEq (BoolE True) (BoolE True)) `shouldBe` True
      val (eval $ PrimBinaryOp PrimNeq (IntE 1) (IntE 2)) `shouldBe` True
      val (eval $ PrimBinaryOp PrimNeq (BoolE True) (BoolE True)) `shouldBe` False
      val (eval $ PrimBinaryOp PrimAnd (BoolE False) (BoolE True)) `shouldBe` False
      val (eval $ PrimBinaryOp PrimOr (BoolE False) (BoolE True)) `shouldBe` True
    it "evaluates selects correct branches" $ do
      val (eval $ Cond (BoolE True) (IntE 2) (IntE 3)) `shouldBe` 2
      val (eval $ Cond (BoolE False) (IntE 2) (IntE 3)) `shouldBe` 3
    it "performs substitution" $ do
      val (eval $ App (Lambda SLInt (PrimUnaryOp PrimNeg (Var Here))) (IntE 42)) `shouldBe` (-42)
      val (eval $ App (App (Lambda SLInt (Lambda SLInt (Var Here))) (IntE 2)) (IntE 3)) `shouldBe` 3
    it "evaluate recursive functions" $ do
      val (eval $ App (Fix (Lambda (SLArrow SLInt SLInt) (Lambda SLInt (Cond (PrimBinaryOp PrimEq (Var Here) (IntE 0)) (IntE 0) (PrimBinaryOp PrimAdd (IntE 2) (App (Var (There Here)) (PrimBinaryOp PrimSub (Var Here) (IntE 1)))))))) (IntE 5)) `shouldBe` 10
      val (eval $ App (App (Fix (Lambda (SLArrow SLInt (SLArrow SLInt SLInt)) (Lambda SLInt (Lambda SLInt (Cond (PrimBinaryOp PrimEq (Var (There Here)) (IntE 0)) (Var Here) (App (App (Var (There (There Here))) (PrimBinaryOp PrimSub (Var (There Here)) (IntE 1))) (PrimBinaryOp PrimAdd (IntE 2) (Var Here)))))))) (IntE 5)) (IntE 0)) `shouldBe` 10
