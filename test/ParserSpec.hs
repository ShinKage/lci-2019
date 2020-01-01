{-# LANGUAGE OverloadedStrings #-}

module ParserSpec where

import Control.Monad
import Data.Singletons
import Data.Text
import Test.Hspec
import Test.Hspec.Megaparsec
import Test.QuickCheck
import Text.Megaparsec

import Lab.Parser
import Lab.Types
import Lab.Untyped

parserSpec :: Spec
parserSpec =
  describe "parsing" $ do
    it "parse integer literals" $ property $
      \x -> if (x :: Integer) >= 0
               then parse (parseLanguage <* eof) "" (pack $ show x) `shouldParse` UIntE x
               else parse (parseLanguage <* eof) "" (pack $ show x) `shouldParse` UPrimUnaryOp PrimNeg (UIntE (abs x))
    it "parse boolean literals" $ do
      parse (parseAtom <* eof) "" "true" `shouldParse` UBoolE True
      parse (parseAtom <* eof) "" "false" `shouldParse` UBoolE False
    it "parse allowed identifiers" $ do
      parse (parseAtom <* eof) "" "abc123_" `shouldParse` UVar "abc123_"
      parse (parseAtom <* eof) "" "abc_123" `shouldParse` UVar "abc_123"
      parse (parseAtom <* eof) "" `shouldFailOn` "_a"
      parse (parseAtom <* eof) "" `shouldFailOn` "2a"
    it "fails for reserved keywords" $ forM_ reserved $
      \k -> parse (identifier <* eof) "" `shouldFailOn` pack k
    it "parse unit literal" $
      parse (parseAtom <* eof) "" "()" `shouldParse` UUnitE
    it "parse conditional branches" $ do
      parse (parseAtom <* eof) "" "if true then 1 else 2" `shouldParse` UCond (UBoolE True) (UIntE 1) (UIntE 2)
      parse (parseAtom <* eof) "" `shouldFailOn` "if true then 1"
    it "parse pairs of expressions" $ do
      parse (parseAtom <* eof) "" "{1, 2}" `shouldParse` UPair (UIntE 1) (UIntE 2)
      parse (parseAtom <* eof) "" "{42, true}" `shouldParse` UPair (UIntE 42) (UBoolE True)
      parse (parseAtom <* eof) "" "{{1, 2}, 3}" `shouldParse` UPair (UPair (UIntE 1) (UIntE 2)) (UIntE 3)
    it "should respect operator precedence" $ do
      parse (parseLanguage <* eof) "" "1 + 2 * 3" `shouldParse` UPrimBinaryOp PrimAdd (UIntE 1) (UPrimBinaryOp PrimMul (UIntE 2) (UIntE 3))
      parse (parseLanguage <* eof) "" "1 <= 2 == true" `shouldParse` UPrimBinaryOp PrimEq (UPrimBinaryOp PrimLE (UIntE 1) (UIntE 2)) (UBoolE True)
      parse (parseLanguage <* eof) "" "~true | false" `shouldParse` UPrimBinaryOp PrimOr (UPrimUnaryOp PrimNot (UBoolE True)) (UBoolE False)
    it "should parse types" $ do
      parse (types <* eof) "" "int" `shouldParse` toSing LInt
      parse (types <* eof) "" "bool" `shouldParse` toSing LBool
      parse (types <* eof) "" "unit" `shouldParse` toSing LUnit
      parse (types <* eof) "" "void" `shouldParse` toSing LVoid
      parse (types <* eof) "" "int -> bool" `shouldParse` toSing (LArrow LInt LBool)
      parse (types <* eof) "" "int -> bool -> int" `shouldParse` toSing (LArrow LInt (LArrow LBool LInt))
      parse (types <* eof) "" "(int -> bool) -> int" `shouldParse` toSing (LArrow (LArrow LInt LBool) LInt)
      parse (types <* eof) "" "{int, bool}" `shouldParse` toSing (LProduct LInt LBool)
      parse (types <* eof) "" "{int, {unit, bool}}" `shouldParse` toSing (LProduct LInt (LProduct LUnit LBool))
    it "should parse fixpoints" $
      parse (fixpoint <* eof) "" "fix 1" `shouldParse` UFix (UIntE 1)
    it "should parse let expressions" $ do
      parse (parseLanguage <* eof) "" "let x:int = 2 in x" `shouldParse` UApp (ULambda "x" (toSing LInt) (UVar "x")) (UIntE 2)
      parse (parseLanguage <* eof) "" "let x:int = let y:int = 2 in y in x" `shouldParse` UApp (ULambda "x" (SomeSing SLInt) (UVar "x")) (UApp (ULambda "y" (SomeSing SLInt) (UVar "y")) (UIntE 2))
    it "should parse lambda abstractions" $ do
      parse (parseLanguage <* eof) "" "\\x:int.x+1" `shouldParse` ULambda "x" (toSing LInt) (UPrimBinaryOp PrimAdd (UVar "x") (UIntE 1))
      parse (parseLanguage <* eof) "" "\\x:int,y:int.x+y" `shouldParse` ULambda "x" (toSing LInt) (ULambda "y" (toSing LInt) (UPrimBinaryOp PrimAdd (UVar "x") (UVar "y")))
      parse (parseLanguage <* eof) "" "\\x:int.\\y:int.x+y" `shouldParse` ULambda "x" (toSing LInt) (ULambda "y" (toSing LInt) (UPrimBinaryOp PrimAdd (UVar "x") (UVar "y")))
