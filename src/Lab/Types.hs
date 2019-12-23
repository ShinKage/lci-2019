{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE UndecidableInstances #-}

-------------------------------------------------------------------------------
-- |
-- Module      : Lab.Types
-- Description : Definitions of Lab types.
-- Copyright   : (c) Giuseppe Lomurno, 2019
-- License     : ...
-- Maintainer  : Giuseppe Lomurno <g.lomurno@studenti.unipi.it>
-- Stability   : experimental
-- Portability : non-portable (?)
--
-------------------------------------------------------------------------------

module Lab.Types where

import Data.Kind
import Data.Singletons.TH
import Data.Text.Prettyprint.Doc

$(singletons [d|
  -- | Lab types.
  data LType = LInt
             | LBool
             | LUnit
             | LVoid
             | LProduct LType LType
             | LArrow LType LType
    deriving (Show, Eq)
  |])

instance Pretty LType where
  pretty LInt  = pretty "ℤ"
  pretty LBool = pretty "𝔹"
  pretty LUnit = pretty "⊤"
  pretty LVoid = pretty "⊥"
  pretty (LProduct a b)   = parens (pretty a <+> pretty "⊗" <+> pretty b)
  pretty (LArrow arg ret) = parens (pretty arg <+> pretty "→" <+> pretty ret)

instance Pretty (SLType ty) where
  pretty = pretty . fromSing

-- | Primitive unary operations with argument and return type.
data UnaryOp :: LType -> LType -> Type where
  PrimNeg :: UnaryOp LInt LInt
  PrimNot :: UnaryOp LBool LBool
  PrimFst :: UnaryOp (LProduct a b) a
  PrimSnd :: UnaryOp (LProduct a b) b

deriving instance Show (UnaryOp arg ret)

-- | Computes the return type of a primitive unary operation.
unaryReturnType :: SLType arg -> UnaryOp arg ret -> SLType ret
unaryReturnType _ PrimNeg = sing
unaryReturnType _ PrimNot = sing
unaryReturnType (SLProduct a _) PrimFst = a
unaryReturnType (SLProduct _ b) PrimSnd = b

instance Pretty (UnaryOp arg ret) where
  pretty PrimNeg = pretty '-'
  pretty PrimNot = pretty '¬'
  pretty PrimFst = pretty "π₁"
  pretty PrimSnd = pretty "π₂"

-- | Primite binary operations with type of the arguments
-- and of the return value.
data BinaryOp :: LType -> LType -> LType -> Type where
  PrimAdd :: BinaryOp LInt LInt LInt
  PrimSub :: BinaryOp LInt LInt LInt
  PrimMul :: BinaryOp LInt LInt LInt
  PrimDiv :: BinaryOp LInt LInt LInt
  PrimAnd :: BinaryOp LBool LBool LBool
  PrimOr  :: BinaryOp LBool LBool LBool
  PrimLT  :: BinaryOp LInt LInt LBool
  PrimGT  :: BinaryOp LInt LInt LBool
  PrimLE  :: BinaryOp LInt LInt LBool
  PrimGE  :: BinaryOp LInt LInt LBool
  PrimEq  :: BinaryOp ty ty LBool
  PrimNeq :: BinaryOp ty ty LBool

deriving instance Show (BinaryOp arg1 arg2 ret)

-- | Computes the return type of a primitive binary operation.
binaryReturnType :: SLType arg1 -> SLType arg2 -> BinaryOp arg1 arg2 ret -> SLType ret
binaryReturnType _ _ PrimAdd = sing
binaryReturnType _ _ PrimSub = sing
binaryReturnType _ _ PrimMul = sing
binaryReturnType _ _ PrimDiv = sing
binaryReturnType _ _ PrimAnd = sing
binaryReturnType _ _ PrimOr = sing
binaryReturnType _ _ PrimLT = sing
binaryReturnType _ _ PrimGT = sing
binaryReturnType _ _ PrimLE = sing
binaryReturnType _ _ PrimGE = sing
binaryReturnType _ _ PrimEq = sing
binaryReturnType _ _ PrimNeq = sing

instance Pretty (BinaryOp arg1 arg2 ret) where
  pretty PrimAdd = pretty '+'
  pretty PrimSub = pretty '-'
  pretty PrimMul = pretty '•'
  pretty PrimDiv = pretty '/'
  pretty PrimAnd = pretty '∧'
  pretty PrimOr  = pretty '∨'
  pretty PrimLT  = pretty '<'
  pretty PrimGT  = pretty '>'
  pretty PrimLE  = pretty '≤'
  pretty PrimGE  = pretty '≥'
  pretty PrimEq  = pretty '='
  pretty PrimNeq = pretty '≠'
