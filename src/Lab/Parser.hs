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
parseLanguage = choice [ let_
                       , fix
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
  , [ prefix "pure" UIOPure
    , prefix "fst" (UPrimUnaryOp PrimFst)
    , prefix "snd" (UPrimUnaryOp PrimSnd)
    ]
  , [binary ">>=" UIOBind]
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
cond = UCond <$> (literal "if" *> parseLanguage)
             <*> (literal "then" *> parseLanguage)
             <*> (literal "else" *> parseLanguage)

parseExpr :: Parser Untyped
parseExpr = foldl1 UApp <$> sepBy1 atom spaceConsumer

atom :: Parser Untyped
atom = try (literal "()" $> UUnitE)
  <|> choice [ parens parseLanguage
             , UIOPrimRead <$> (literal "read" >> types)
             , UIntE <$> lexeme L.decimal
             , UBoolE <$> ((literal "true" $> True) <|> (literal "false" $> False))
             , cond
             , UVar <$> identifier
             , pair
             ]

identifier :: Parser Text
identifier = pack <$> (lexeme . try) (p >>= check)
  where p = (:) <$> letterChar <*> many (alphaNumChar <|> char '_') <?> "variable"
        check x = if x `elem` reserved
                     then fail $ "reserved keyword " ++ show x ++ " cannot be an identifier"
                     else pure x

typeArrow :: Operator Parser (SomeSing LType)
typeArrow = InfixR $ from <$ literal "->"
  where
    from (SomeSing ty1) (SomeSing ty2) = toSing $ LArrow (fromSing ty1) (fromSing ty2)

ioType :: Operator Parser (SomeSing LType)
ioType = Prefix $ from <$ literal "IO"
  where
    from (SomeSing ty) = toSing $ LIO $ fromSing ty

fix :: Parser Untyped
fix = UFix <$> (literal "fix" *> parseLanguage)

lambda :: Parser Untyped
lambda = do
  literal "\\"
  args <- sepBy1 annotatedType (literal ",")
  literal "."
  body <- parseLanguage
  pure $ foldr (uncurry ULambda) body args

let_ :: Parser Untyped
let_ = do
  literal "let"
  name <- identifier
  literal ":"
  ty <- types
  literal "="
  e1 <- parseLanguage
  literal "in"
  e2 <- parseLanguage
  pure $ UApp (ULambda name ty e2) e1

pair :: Parser Untyped
pair = curly $ UPair <$> parseLanguage <*> (literal "," *> parseLanguage)

types :: Parser (SomeSing LType)
types = makeExprParser typeExpr [[arrow]]

arrow :: Operator Parser (SomeSing LType)
arrow = InfixR $ from <$ literal "->"
  where
    from (SomeSing ty1) (SomeSing ty2) = toSing $ LArrow (fromSing ty1) (fromSing ty2)

typeExpr :: Parser (SomeSing LType)
typeExpr = choice [ parens types
                  , literal "int"  $> toSing LInt
                  , literal "bool" $> toSing LBool
                  , literal "unit" $> toSing LUnit
                  , literal "void" $> toSing LVoid
                  , pairType
                  ]

pairType :: Parser (SomeSing LType)
pairType = curly $ do
  SomeSing ty1 <- types
  literal ","
  SomeSing ty2 <- types
  pure . toSing $ LProduct (fromSing ty1) (fromSing ty2)

annotatedType :: Parser (Name, SomeSing LType)
annotatedType = (,) <$> identifier <*> (literal ":" *> types)

reserved :: [String]
reserved = [ "if", "then", "else"
           , "let", "in"
           , "int", "bool", "unit", "void"
           , "true", "false"
           , "fst", "snd"
           , "io", "bind", "pure"
           ]
