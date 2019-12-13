{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}

-------------------------------------------------------------------------------
-- |
-- Module      : Lab.Decls
-- Description : Lab language abstract syntax tree with top-level
--               function declarations
-- Copyright   : (c) Giuseppe Lomurno, 2019
-- License     : ...
-- Maintainer  : Giuseppe Lomurno <g.lomurno@studenti.unipi.it>
-- Stability   : experimental
-- Portability : non-portable (?)
--
-------------------------------------------------------------------------------

module Lab.Decls where

import Data.Kind
import Data.Nat
import Data.List.Extra
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal
import Data.Text.Prettyprint.Doc.Symbols.Unicode

import Lab.Types
import Lab.Utils

data CodegenAST :: Type where
  CIntE  :: Integer -> CodegenAST
  CBoolE :: Bool -> CodegenAST
  CUnitE :: CodegenAST
  CPrimUnaryOp :: UnaryOp arg ret -> CodegenAST -> CodegenAST
  CPrimBinaryOp :: BinaryOp arg1 arg2 ret -> CodegenAST -> CodegenAST -> CodegenAST
  CCond :: CodegenAST -> CodegenAST -> CodegenAST -> CodegenAST
  CVar :: Int -> CodegenAST
  CPair :: CodegenAST -> CodegenAST -> CodegenAST
  CCall :: Int -> [CodegenAST] -> CodegenAST
deriving instance Show CodegenAST

data Declaration = Decl { argsType :: [LType]
                        , retType :: LType
                        , body :: CodegenAST
                        }
  deriving (Show)

data CodegenEnv = Env { decl :: [Declaration]
                      , expr :: CodegenAST
                      }
  deriving (Show)
