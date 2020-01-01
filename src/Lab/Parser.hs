{-# LANGUAGE OverloadedStrings #-}

-------------------------------------------------------------------------------
-- |
-- Module      : Lab.Parser
-- Description : Parser combinator definition for Lab.
-- Copyright   : (c) Giuseppe Lomurno, 2019
-- License     : ...
-- Maintainer  : Giuseppe Lomurno <g.lomurno@studenti.unipi.it>
-- Stability   : experimental
-- Portability : non-portable (?)
--
-------------------------------------------------------------------------------

module Lab.Parser where

import           Control.Monad.Combinators.Expr
import           Data.Functor (($>))
import           Data.Singletons
import           Data.Text (Text, pack)
import           Data.Void
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import           Lab.Types
import           Lab.Untyped

-- TODO: Custom error messages
type Parser = Parsec Void Text

parseLanguage :: Parser Untyped
parseLanguage = choice [ parseLet
                       , fixpoint
                       , lambda
                       , makeExprParser parseExpr operatorTable
                       ]

spaceConsumer :: Parser ()
spaceConsumer =
  L.space space1 (L.skipLineComment "//") (L.skipBlockComment "/*" "*/")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

literal :: Text -> Parser ()
literal sym = L.symbol spaceConsumer sym $> ()

parens :: Parser a -> Parser a
parens = between (literal "(") (literal ")")

curly :: Parser a -> Parser a
curly = between (literal "{") (literal "}")

operatorTable :: [[Operator Parser Untyped]]
operatorTable =
  [ [prefix "-" (UPrimUnaryOp PrimNeg), prefix "~" (UPrimUnaryOp PrimNot)]
  , [prefix "fst" (UPrimUnaryOp PrimFst), prefix "snd" (UPrimUnaryOp PrimSnd)]
  , [binary "*" (UPrimBinaryOp PrimMul), binary "/" (UPrimBinaryOp PrimDiv)]
  , [binary "+" (UPrimBinaryOp PrimAdd), binary "-" (UPrimBinaryOp PrimSub)]
  , [ binary "<=" (UPrimBinaryOp PrimLE)
    , binary "<"  (UPrimBinaryOp PrimLT)
    , binary ">=" (UPrimBinaryOp PrimGE)
    , binary ">"  (UPrimBinaryOp PrimGT)
    ]
  , [binary "==" (UPrimBinaryOp PrimEq), binary "!=" (UPrimBinaryOp PrimNeq)]
  , [binary "&" (UPrimBinaryOp PrimAnd)]
  , [binary "|" (UPrimBinaryOp PrimOr)]
  ]

binary :: Text -> (Untyped -> Untyped -> Untyped) -> Operator Parser Untyped
binary name f = InfixL (f <$ literal name)

prefix :: Text -> (Untyped -> Untyped) -> Operator Parser Untyped
prefix name f = Prefix (f <$ literal name)

cond :: Parser Untyped
cond = UCond <$> (tokIf *> parseLanguage) <*> (tokThen *> parseLanguage) <*> (tokElse *> parseLanguage)

parseExpr :: Parser Untyped
parseExpr = foldl1 UApp <$> sepBy1 parseAtom spaceConsumer

parseAtom :: Parser Untyped
parseAtom = try (tokUnit $> UUnitE) <|> choice [ parens parseLanguage
                   , UIntE <$> lexeme L.decimal
                   , UBoolE <$> ((tokTrue $> True) <|> (tokFalse $> False))
                   , cond
                   , UVar <$> identifier
                   , pair
                   ]

reserved :: [String]
reserved = ["if", "then", "else", "let", "in", "int", "bool", "unit", "true", "false", "void"]

identifier :: Parser Text
identifier = pack <$> (lexeme . try) (p >>= check)
  where p = (:) <$> letterChar <*> many (alphaNumChar <|> char '_') <?> "variable"
        check x = if x `elem` reserved
                     then fail $ "keyword " ++ show x ++ " cannot be an identifier"
                     else pure x

types :: Parser (SomeSing LType)
types = makeExprParser typeExpr [[typeArrow]]

typeArrow :: Operator Parser (SomeSing LType)
typeArrow = InfixR $ from <$ tokArrow
  where
    from (SomeSing ty1) (SomeSing ty2) = toSing (LArrow (fromSing ty1) (fromSing ty2))

typeExpr :: Parser (SomeSing LType)
typeExpr = choice [ parens types
                  , tokIntType $> toSing LInt
                  , tokBoolType $> toSing LBool
                  , tokUnitType $> toSing LUnit
                  , tokVoidType $> toSing LVoid
                  , pairType
                  ]

pairType :: Parser (SomeSing LType)
pairType = curly $ do
  SomeSing l <- types
  tokComma
  SomeSing r <- types
  pure . toSing $ LProduct (fromSing l) (fromSing r)

fixpoint :: Parser Untyped
fixpoint = UFix <$> (tokFix *> parseLanguage)

lambda :: Parser Untyped
lambda = do
  tokLambda
  args <- sepBy1 annotatedType tokComma
  tokDot
  body <- parseLanguage
  pure $ foldr (\(name, ty) acc -> ULambda name ty acc) body args
    where annotatedType = (,) <$> identifier <*> (tokColon *> types)

parseLet :: Parser Untyped
parseLet = do
  tokLet
  name <- identifier
  tokColon
  ty <- types
  tokEqual
  e1 <- parseLanguage
  tokIn
  e2 <- parseLanguage
  pure $ UApp (ULambda name ty e2) e1

pair :: Parser Untyped
pair = curly $ UPair <$> parseLanguage <*> (tokComma *> parseLanguage)

-------------------------------------------------------------------------------
-- * Tokens
-------------------------------------------------------------------------------

tokLambda :: Parser ()
tokLambda = literal "\\"

tokComma :: Parser ()
tokComma = literal ","

tokColon :: Parser ()
tokColon = literal ":"

tokDot :: Parser ()
tokDot = literal "."

tokIn :: Parser ()
tokIn = literal "in"

tokEqual :: Parser ()
tokEqual = literal "="

tokLet :: Parser ()
tokLet = literal "let"

tokUnit :: Parser ()
tokUnit = literal "()"

tokTrue :: Parser ()
tokTrue = literal "true"

tokFalse :: Parser ()
tokFalse = literal "false"

tokFix :: Parser ()
tokFix = literal "fix"

tokIntType :: Parser ()
tokIntType = literal "int"

tokBoolType :: Parser ()
tokBoolType = literal "bool"

tokUnitType :: Parser ()
tokUnitType = literal "unit"

tokVoidType :: Parser ()
tokVoidType = literal "void"

tokArrow :: Parser ()
tokArrow = literal "->"

tokIf :: Parser ()
tokIf = literal "if"

tokElse :: Parser ()
tokElse = literal "else"

tokThen :: Parser ()
tokThen = literal "then"
