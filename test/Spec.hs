import Test.Hspec

import EvalSpec
import ParserSpec
import TypecheckSpec

main :: IO ()
main = hspec $ do
  parserSpec
  typecheckSpec
  evalSpec
