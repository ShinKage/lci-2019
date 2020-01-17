{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
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

module Lab.AST where

import Control.Monad.Reader
import Data.Kind
import Data.List.Extra
import Data.Singletons.Prelude hiding (Elem)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal
import Data.Text.Prettyprint.Doc.Symbols.Unicode

import Lab.Types
import Lab.Utils

-- | The Lab language Abstract Syntax Tree.
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
  -- | Lambda abstraction with explicit argument type.
  Lambda :: SLType arg -> AST (arg : env) ret -> AST env (LArrow arg ret)
  -- | Variable as De Brujin index of the indexed binding list.
  Var :: Elem env ty -> AST env ty
  -- | Lambda application.
  App :: AST env (LArrow arg ret) -> AST env arg -> AST env ret
  -- | Pair of expressions.
  Pair :: AST env a -> AST env b -> AST env (LProduct a b)
  -- | Fixpoint operator for recursive functions support.
  Fix :: AST env (LArrow a a) -> AST env a
  -- | Pure IO operation.
  IOPure :: AST env a -> AST env (LIO a)
  -- | IO monadic composition.
  IOBind :: AST env (LIO a) -> AST env (LArrow a (LIO b)) -> AST env (LIO b)
  IOPrimRead :: SLType a -> AST env (LIO a)
  -- IOPrimShow :: AST env a -> AST env (LIO LUnit)

deriving instance Show (AST env ty)

-- | Computes the return type of an expression within an environment.
returnType :: SList env -> AST env ty -> SLType ty
returnType _ (IntE _)  = sing
returnType _ (BoolE _) = sing
returnType _ UnitE     = sing
returnType env (PrimUnaryOp op e) = unaryReturnType (returnType env e) op
returnType env (PrimBinaryOp op e1 e2) = binaryReturnType (returnType env e1) (returnType env e2) op
returnType env (Cond _ e1 _) = returnType env e1
returnType env (Lambda ty body) = SLArrow ty (returnType (SCons ty env) body)
returnType env (Var e) = index e env
returnType env (App lam _) = case returnType env lam of SLArrow _ ty -> ty
returnType env (Fix e) = case returnType env e of SLArrow _ ty -> ty
returnType env (Pair e1 e2) = SLProduct (returnType env e1) (returnType env e2)
returnType env (IOPure e) = SLIO (returnType env e)
returnType env (IOBind _ e2) = case returnType env e2 of SLArrow _ ty -> ty
returnType _ (IOPrimRead ty) = SLIO ty
-- returnType _ (IOPrimShow e) = SLIO SLUnit

prettyAST :: AST '[] ty -> Doc AnsiStyle
prettyAST = prettyAST' SNil

prettyAST' :: SList env -> AST env ty -> Doc AnsiStyle
prettyAST' types = flip runReader initPrec . go types
  where go :: SList env -> AST env ty -> Reader Prec (Doc AnsiStyle)
        go _ (IntE n) = pure $ annotate bold (pretty n)
        go _ (BoolE b) = pure $ annotate bold (pretty b)
        go _ UnitE = pure $ annotate bold (pretty "unit")
        go env (PrimUnaryOp op e) = do
          e' <- local (const $ opPrecArg op) $ go env e
          prec <- ask
          pure $ maybeParens (prec >= opPrec op) e'
        go env (PrimBinaryOp op e1 e2) = do
          e1' <- local (const $ binOpLeftPrec op) $ go env e1
          e2' <- local (const $ binOpRightPrec op) $ go env e2
          prec <- ask
          pure $ maybeParens (prec >= binOpPrec op) $ fillSep [e1' <+> pretty op, e2']
        go env (Cond c e1 e2) = do
          c' <- local (const initPrec) $ go env c
          e1' <- local (const initPrec) $ go env e1
          e2' <- local (const initPrec) $ go env e2
          prec <- ask
          pure $ maybeParens (prec >= ifPrec) $
            fillSep [ pretty "if" <+> c'
                    , pretty "then" <+> e1'
                    , pretty "else" <+> e2'
                    ]
        go env (Var (elemToIntegral -> v)) = do
          let i = sLength env - v - 1
          pure $ colorVar i $ pretty '#' <> pretty i
        go env (Lambda ty body) = do
          body' <- local (const initPrec) $ go (SCons ty env) body
          let i = sLength env
          prec <- ask
          pure $ maybeParens (prec >= lambdaPrec) $
            fillSep [ pretty 'λ' <> colorVar i (pretty '#' <> pretty i) <+> pretty ':'
                                 <+> pretty ty <> pretty '.'
                    , body'
                    ]
        go env (App body arg) = do
          body' <- local (const appLeftPrec) $ go env body
          arg' <- local (const appRightPrec) $ go env arg
          prec <- ask
          pure $ maybeParens (prec >= appPrec) $ body' <+> arg'
        go env (Pair f s) = do
          f' <- local (const initPrec) $ go env f
          s' <- local (const initPrec) $ go env s
          pure $ sGuillemetsOut $ f' <> comma <> s'
        go env (Fix body) = do
          body' <- local (const initPrec) $ go env body
          prec <- ask
          pure $ maybeParens (prec >= appPrec) $ pretty "fix" <+> body'
        go env (IOPure e) = do
          e' <- local (const initPrec) $ go env e
          prec <- ask
          pure $ maybeParens (prec >= appPrec) $ pretty "pure" <+> e'
        go env (IOBind e1 e2) = do
          e1' <- local (const initPrec) $ go env e1
          e2' <- local (const initPrec) $ go env e2
          prec <- ask
          pure $ maybeParens (prec >= initPrec) $ e1' <+> pretty ">>=" <+> e2'
        go env (IOPrimRead ty) = pure $ pretty "read" <+> pretty ty
--         go env (IOPrimShow e) = do
--           e' <- local (const initPrec) $ go env e
--           prec <- ask
--           pure $ maybeParens (prec >= appPrec) $ pretty "show " <+> e'
