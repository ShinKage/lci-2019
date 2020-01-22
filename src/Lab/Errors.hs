-------------------------------------------------------------------------------
-- |
-- Module      : Lab.Errors
-- Description : Lab language errors.
-- Copyright   : (c) Giuseppe Lomurno, 2019
-- License     : ...
-- Maintainer  : Giuseppe Lomurno <g.lomurno@studenti.unipi.it>
-- Stability   : experimental
-- Portability : non-portable (?)
--
-------------------------------------------------------------------------------

module Lab.Errors where

import Data.Singletons
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal

import Lab.Types

-- | Lab language errors.
data LabError
  -- | Expression required a type but got another.
  = ExpectedType (SomeSing LType) (SomeSing LType) String
  -- | Two expression require same type but got two distinct types.
  | TypeMismatch (SomeSing LType) (SomeSing LType) String
  -- | Expression is required to represent a lambda abstraction.
  | LambdaRequired (SomeSing LType) String
  -- | Expression is required to represent a pair.
  | PairRequired (SomeSing LType) String
  -- | Parsing error, name reference is undefined.
  | UndefinedReference String
  -- | Unsupported expression in Fix operator.
  | UnsupportedFix String
  -- | Generic parsing error.
  | ParseError String
  -- | Generic code generation error.
  | CodegenError String
  deriving (Eq, Show)

prettyError :: LabError -> Doc AnsiStyle
prettyError (ExpectedType (SomeSing t1) (SomeSing t2) msg) =
  vcat [ pretty "Expected type error:"
       , indent 2 $ pretty "Expected type:" <+> annotate (color Green) (pretty t1)
       , indent 2 $ pretty "Actual type:" <+> annotate (color Red) (pretty t2)
       , pretty msg
       ]
prettyError (TypeMismatch (SomeSing t1) (SomeSing t2) msg) =
  vcat [ pretty "Type mismatch between two equal branches:"
       , indent 2 $ pretty "First expression type:" <+> annotate (color Red) (pretty t1)
       , indent 2 $ pretty "Second expression type:" <+> annotate (color Red) (pretty t2)
       , pretty msg
       ]
prettyError (LambdaRequired (SomeSing t) msg) =
  vcat [ pretty "Lambda required, instead got type:"
       , indent 2 $ annotate (color Red) (pretty t)
       , pretty msg
       ]
prettyError (PairRequired (SomeSing t) msg) =
  vcat [ pretty "Pair required, instead got type:"
       , indent 2 $ annotate (color Red) (pretty t)
       , pretty msg
       ]
prettyError (UndefinedReference name) =
  pretty "The name" <+> dquotes (annotate (color Red) (pretty name)) <+> pretty "is undefined in this context"
prettyError (ParseError msg) = pretty msg
prettyError (CodegenError msg) = pretty msg
prettyError (UnsupportedFix msg) = pretty msg

expectedType :: SLType t1 -> SLType t2 -> String -> LabError
expectedType st1 st2 = ExpectedType (SomeSing st1) (SomeSing st2)

typeMismatch :: SLType t1 -> SLType t2 -> String -> LabError
typeMismatch st1 st2 = TypeMismatch (SomeSing st1) (SomeSing st2)

lambdaRequired :: SLType t1 -> String -> LabError
lambdaRequired st1 = LambdaRequired (SomeSing st1)

pairRequired :: SLType t1 -> String -> LabError
pairRequired st1 = PairRequired (SomeSing st1)

undefReference :: String -> LabError
undefReference = UndefinedReference

parseError :: String -> LabError
parseError = ParseError

unsupportedFix :: String -> LabError
unsupportedFix = UnsupportedFix
