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
import Data.Hashable
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

instance Hashable LType where
  hashWithSalt s LInt = s `hashWithSalt` (0 :: Int)
  hashWithSalt s LBool = s `hashWithSalt` (1 :: Int)
  hashWithSalt s LUnit = s `hashWithSalt` (2 :: Int)
  hashWithSalt s LVoid = s `hashWithSalt` (3 :: Int)
  hashWithSalt s (LProduct a b) = s `hashWithSalt` (4 :: Int)
                                    `hashWithSalt` a
                                    `hashWithSalt` b
  hashWithSalt s (LArrow a b) = s `hashWithSalt` (5 :: Int)
                                  `hashWithSalt` a
                                  `hashWithSalt` b

instance Hashable (SLType ty) where
  hashWithSalt s ty = hashWithSalt s (fromSing ty)

-- | Primitive unary operations with argument and return type.
data UnaryOp :: LType -> LType -> Type where
  PrimNeg :: UnaryOp LInt LInt
  PrimNot :: UnaryOp LBool LBool
  PrimFst :: UnaryOp (LProduct a b) a
  PrimSnd :: UnaryOp (LProduct a b) b

deriving instance Show (UnaryOp arg ret)

eqUnary :: UnaryOp a b -> UnaryOp c d -> Bool
eqUnary PrimNeg PrimNeg = True
eqUnary PrimNot PrimNot = True
eqUnary PrimFst PrimFst = True
eqUnary PrimSnd PrimSnd = True
eqUnary _ _ = False

instance Hashable (UnaryOp arg ret) where
  hashWithSalt s PrimNeg = s `hashWithSalt` (0 :: Int)
  hashWithSalt s PrimNot = s `hashWithSalt` (1 :: Int)
  hashWithSalt s PrimFst = s `hashWithSalt` (2 :: Int)
  hashWithSalt s PrimSnd = s `hashWithSalt` (3 :: Int)

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

eqBinary :: BinaryOp a b c -> BinaryOp d e f -> Bool
eqBinary PrimAdd PrimAdd = True
eqBinary PrimSub PrimSub = True
eqBinary PrimMul PrimMul = True
eqBinary PrimDiv PrimDiv = True
eqBinary PrimAnd PrimAnd = True
eqBinary PrimOr PrimOr = True
eqBinary PrimLT PrimLT = True
eqBinary PrimGT PrimGT = True
eqBinary PrimLE PrimLE = True
eqBinary PrimGE PrimGE = True
eqBinary PrimEq PrimEq = True
eqBinary PrimNeq PrimNeq = True
eqBinary _ _ = False

instance Hashable (BinaryOp arg1 arg2 ret) where
  hashWithSalt s PrimAdd = s `hashWithSalt` (0 :: Int)
  hashWithSalt s PrimSub = s `hashWithSalt` (1 :: Int)
  hashWithSalt s PrimMul = s `hashWithSalt` (2 :: Int)
  hashWithSalt s PrimDiv = s `hashWithSalt` (3 :: Int)
  hashWithSalt s PrimAnd = s `hashWithSalt` (4 :: Int)
  hashWithSalt s PrimOr = s `hashWithSalt` (5 :: Int)
  hashWithSalt s PrimLT = s `hashWithSalt` (6 :: Int)
  hashWithSalt s PrimGT = s `hashWithSalt` (7 :: Int)
  hashWithSalt s PrimLE = s `hashWithSalt` (8 :: Int)
  hashWithSalt s PrimGE = s `hashWithSalt` (9 :: Int)
  hashWithSalt s PrimEq = s `hashWithSalt` (10 :: Int)
  hashWithSalt s PrimNeq = s `hashWithSalt` (11 :: Int)

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
