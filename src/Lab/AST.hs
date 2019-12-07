{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}

-------------------------------------------------------------------------------
-- |
-- Module      : Lab.AST
-- Description : Lab language abstract syntax tree.
-- Copyright   : (c) Giuseppe Lomurno, 2019
-- License     : ...
-- Maintainer  : Giuseppe Lomurno <g.lomurno@studenti.unipi.it>
-- Stability   : experimental
-- Portability : non-portable (?)
--
-------------------------------------------------------------------------------

module Lab.AST (AST(..)) where

import Data.Kind
import Data.List.Extra
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Symbols.Unicode

import Lab.Types
import Lab.Utils

-- | The lab language Abstract Syntax Tree.
-- The data type is indexed by the list of binded types and the return type
-- of the expression. Dependent functionalities are used to constructs only
-- well-formed expressions, in particular regarding to typing rules.
data AST :: [LType] -> LType -> Type where
  -- | An integer literal.
  IntE  :: Integer -> AST env LInt
  -- | A boolean literal.
  BoolE :: Bool -> AST env LBool
  -- | Unit literal.
  UnitE :: AST env LUnit
  -- | Primitive unary operators.
  PrimUnaryOp :: UnaryOp arg ret -> AST env arg -> AST env ret
  -- | Primitive binary operators.
  PrimBinaryOp :: BinaryOp arg1 arg2 ret -> AST env arg1 -> AST env arg2 -> AST env ret
  -- | Conditional expressions, all branches must have the same type.
  Cond :: AST env LBool -> AST env ret -> AST env ret -> AST env ret
  -- | Lambda abstraction with explicit type. In some context the type singleton
  -- can be inferred thanks to the 'SingI' class.
  Lambda :: SLType arg -> AST (arg : env) ret -> AST env (LArrow arg ret)
  -- | Variable as De Brujin index of the indexed binding list.
  Var :: Elem env ty -> AST env ty
  -- | Lambda application.
  App :: AST env (LArrow arg ret) -> AST env arg -> AST env ret
  -- | Pair of expressions.
  Pair :: AST env a -> AST env b -> AST env (LProduct a b)
  -- | Fixpoint operator for recursive functions
  Fix :: AST env (LArrow a a) -> AST env a
deriving instance Show (AST env ty)

instance Pretty (AST '[] ty) where
  pretty = prettyAST

-- | Pretty printing for the AST.
prettyAST :: AST env ty -> Doc ann
prettyAST = snd . go 0 initPrec
 where
  go :: Int -> Rational -> AST env ty -> (Int, Doc ann)
  go i _ (IntE  n) = (i, pretty n)
  go i _ (BoolE b) = (i, pretty b)
  go i _ UnitE     = (i, pretty "unit")
  go i prec (PrimUnaryOp op e1) =
    (i, maybeParens (prec >= opPrec op) $ pretty op <> snd (go i (opPrecArg op) e1))
  go i prec (PrimBinaryOp op e1 e2) =
    (i, maybeParens (prec >= binOpPrec op) $
          snd (go i (binOpLeftPrec op) e1)
          <+> pretty op
          <+> snd (go i (binOpRightPrec op) e2))
  go i prec (Cond c e1 e2) =
    (i, maybeParens (prec >= ifPrec) $ fillSep
      [ pretty "if"   <+> snd (go i initPrec c)
      , pretty "then" <+> snd (go i initPrec e1)
      , pretty "else" <+> snd (go i initPrec e2)
      ])
  go i _ (Var v) = (i, pretty '#' <> pretty (elemToIntegral v :: Integer))
  go i prec (Lambda ty body) = case go i initPrec body of
    (i_body, doc_body) ->
      (i + 1, maybeParens (prec >= lambdaPrec) $
        fillSep [ pretty 'λ' <> pretty '#' <> pretty i_body <+> pretty ':'
                             <+> pretty ty <> pretty '.'
                , doc_body
                ])
  go i prec (App body arg) = (i, maybeParens (prec >= appPrec) $
    snd (go i appLeftPrec body) <+> snd (go i appRightPrec arg))
  go i _ (Pair f s) = (i, sGuillemetsOut $
    snd (go i initPrec f) <> comma <> snd (go i initPrec s))
  go i prec (Fix body) = (i, maybeParens (prec >= appPrec) $
    pretty "fix" <+> snd (go i initPrec body))
