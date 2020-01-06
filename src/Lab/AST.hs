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

import Control.Monad.State.Strict
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

prettyAST :: AST env ty -> Doc AnsiStyle
prettyAST = flip evalState (0, initPrec) . go
  where updatePrec :: Prec -> (Int, Prec) -> (Int, Prec)
        updatePrec p (i, _) = (i, p)

        go :: AST env ty -> State (Int, Prec) (Doc AnsiStyle)
        go (IntE n) = pure $ annotate bold (pretty n)
        go (BoolE b) = pure $ annotate bold (pretty b)
        go UnitE = pure $ annotate bold (pretty "unit")
        go (PrimUnaryOp op e) = do
          prec <- gets snd
          e' <- withState (updatePrec $ opPrecArg op) $ go e
          pure $ maybeParens (prec >= opPrec op) e'
        go (PrimBinaryOp op e1 e2) = do
          prec <- gets snd
          e1' <- withState (updatePrec $ binOpLeftPrec op) $ go e1
          e2' <- withState (updatePrec $ binOpRightPrec op) $ go e2
          pure $ maybeParens (prec >= binOpPrec op) $ fillSep [e1' <+> pretty op, e2']
        go (Cond c e1 e2) = do
          prec <- gets snd
          c' <- withState (updatePrec initPrec) $ go c
          e1' <- withState (updatePrec initPrec) $ go e1
          e2' <- withState (updatePrec initPrec) $ go e2
          pure $ maybeParens (prec >= ifPrec) $
            fillSep [ pretty "if" <+> c'
                    , pretty "then" <+> e1'
                    , pretty "else" <+> e2'
                    ]
        go (Var (elemToIntegral -> v)) = pure $ colorVar v $ pretty '#' <> pretty v
        go (Lambda ty body) = do
          prec <- gets snd
          old <- gets fst
          body' <- withState (updatePrec initPrec) $ go body
          i <- gets fst
          modify $ \(_, p) -> (old + 1, p)
          pure $ maybeParens (prec >= lambdaPrec) $
            fillSep [ pretty 'λ' <> colorVar i (pretty '#' <> pretty i) <+> pretty ':'
                                 <+> pretty ty <> pretty '.'
                    , body'
                    ]
        go (App body arg) = do
          prec <- gets snd
          body' <- withState (updatePrec appLeftPrec) $ go body
          arg' <- withState (updatePrec appRightPrec) $ go arg
          pure $ maybeParens (prec >= appPrec) $ body' <+> arg'
        go (Pair f s) = do
          f' <- withState (updatePrec initPrec) $ go f
          s' <- withState (updatePrec initPrec) $ go s
          pure $ sGuillemetsOut $ f' <> comma <> s'
        go (Fix body) = do
          prec <- gets snd
          body' <- withState (updatePrec initPrec) $ go body
          pure $ maybeParens (prec >= appPrec) $ pretty "fix" <+> body'
