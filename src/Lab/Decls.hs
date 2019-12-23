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
--               function declarations, ready for code generation.
-- Copyright   : (c) Giuseppe Lomurno, 2019
-- License     : ...
-- Maintainer  : Giuseppe Lomurno <g.lomurno@studenti.unipi.it>
-- Stability   : experimental
-- Portability : non-portable (?)
--
-------------------------------------------------------------------------------

module Lab.Decls ( CodegenAST(..)
                 , Declaration(..)
                 , CodegenEnv(..)
                 , closureConv
                 , freeVars
                 , fromAST
                 , liftLam
                 , prettyCodegenAST
                 , smash) where

import Control.Monad.Writer
import Control.Monad.State
import qualified Control.Monad.State.Strict as Strict
import Data.Kind
import Data.List.Extra
import Data.Singletons.Prelude
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal
import Data.Text.Prettyprint.Doc.Symbols.Unicode

import Lab.AST
import Lab.Types
import Lab.Utils

-- | Stripped down version of the Lab AST, with support for top level
-- function declarations and call mechanism. This IR is not typed and
-- is meant to be derived only by translation from the typed AST.
data CodegenAST :: Type where
  -- | An integer literal.
  CIntE  :: Integer -> CodegenAST
  -- | A boolean literal.
  CBoolE :: Bool -> CodegenAST
  -- | Unit literal.
  CUnitE :: CodegenAST
  -- | Primitive unary operators.
  CPrimUnaryOp :: UnaryOp arg ret -> CodegenAST -> CodegenAST
  -- | Primitive binary operators.
  CPrimBinaryOp :: BinaryOp arg1 arg2 ret -> CodegenAST -> CodegenAST -> CodegenAST
  -- | Conditional expressions.
  CCond :: CodegenAST -> CodegenAST -> CodegenAST -> CodegenAST
  -- | Variable as De Brujin index of the environment.
  CVar :: Int -> CodegenAST
  -- | Pair of expressions.
  CPair :: CodegenAST -> CodegenAST -> CodegenAST
  -- | Reference to a top-level function declaration.
  CCall :: Int -> CodegenAST
  -- | Lambda abstraction with explicit arguments type.
  CLambda :: [LType] -> LType -> CodegenAST -> CodegenAST
  -- | Lambda application. It only applies a single argument.
  CApp :: CodegenAST -> CodegenAST -> CodegenAST
  -- | Fixpoint operator for recursive functions support.
  -- Correctly lifted expression must not contain this constructor.
  CFix :: CodegenAST -> CodegenAST
  -- Recursion call token, must be present only in top-level declarations.
  CRecToken :: CodegenAST

deriving instance Show CodegenAST

-- | A top-level function declaration.
data Declaration = Decl { argsType :: [LType]
                        , retType :: LType
                        , body :: CodegenAST
                        }
  deriving (Show)

-- | An environment for code generation with a list of declarations
-- and the expression to execute.
data CodegenEnv = Env { decl :: [Declaration]
                      , expr :: CodegenAST
                      }
  deriving (Show)

prettyCodegenAST :: CodegenAST -> Doc AnsiStyle
prettyCodegenAST = flip Strict.evalState (0, initPrec) . go
  where updatePrec :: Prec -> (Int, Prec) -> (Int, Prec)
        updatePrec p (i, _) = (i, p)

        go :: CodegenAST -> Strict.State (Int, Prec) (Doc AnsiStyle)
        go (CIntE n) = pure $ annotate bold (pretty n)
        go (CBoolE b) = pure $ annotate bold (pretty b)
        go CUnitE = pure $ annotate bold (pretty "unit")
        go (CPrimUnaryOp op e) = do
          prec <- gets snd
          e' <- Strict.withState (updatePrec $ opPrecArg op) $ go e
          pure $ maybeParens (prec >= opPrec op) e'
        go (CPrimBinaryOp op e1 e2) = do
          prec <- gets snd
          e1' <- Strict.withState (updatePrec $ binOpLeftPrec op) $ go e1
          e2' <- Strict.withState (updatePrec $ binOpRightPrec op) $ go e2
          pure $ maybeParens (prec >= binOpPrec op) $ fillSep [e1' <+> pretty op, e2']
        go (CCond c e1 e2) = do
          prec <- gets snd
          c' <- Strict.withState (updatePrec initPrec) $ go c
          e1' <- Strict.withState (updatePrec initPrec) $ go e1
          e2' <- Strict.withState (updatePrec initPrec) $ go e2
          pure $ maybeParens (prec >= ifPrec) $
            fillSep [ pretty "if" <+> c'
                    , pretty "then" <+> e1'
                    , pretty "else" <+> e2'
                    ]
        go (CVar v) = pure $ colorVar v $ pretty '#' <> pretty v
        go (CCall v) = pure $ pretty "call" <+> pretty v
        go (CLambda args _ e) = do
          prec <- gets snd
          old <- gets fst
          e' <- Strict.withState (updatePrec initPrec) $ go e
          modify $ \(_, p) -> (old + 1, p)
          pure $ maybeParens (prec >= lambdaPrec) $
            fillSep [ pretty 'λ' <+> pretty args <> pretty '.'
                    , e'
                    ]
        go (CApp e arg) = do
          prec <- gets snd
          e' <- Strict.withState (updatePrec appLeftPrec) $ go e
          arg' <- Strict.withState (updatePrec appRightPrec) $ go arg
          pure $ maybeParens (prec >= appPrec) $ e' <+> arg'
        go (CPair f s) = do
          f' <- Strict.withState (updatePrec initPrec) $ go f
          s' <- Strict.withState (updatePrec initPrec) $ go s
          pure $ sGuillemetsOut $ f' <> comma <> s'
        go (CFix e) = do
          prec <- gets snd
          e' <- Strict.withState (updatePrec initPrec) $ go e
          pure $ maybeParens (prec >= appPrec) $ pretty "fix" <+> e'
        go CRecToken = pure $ pretty "rec call"

-- | Conversion from a typed AST to a code generation ready IR.
fromAST :: SList env -> AST env ty -> CodegenAST
fromAST = fromAST' 0

fromAST' :: Int -> SList env -> AST env ty -> CodegenAST
fromAST' vars env (PrimUnaryOp op e) = CPrimUnaryOp op (fromAST' vars env e)
fromAST' vars env (PrimBinaryOp op e1 e2) = CPrimBinaryOp op (fromAST' vars env e1) (fromAST' vars env e2)
fromAST' vars env (Cond c e1 e2) = CCond (fromAST' vars env c) (fromAST' vars env e1) (fromAST' vars env e2)
fromAST' vars _   (Var e) = if vars == elemToIntegral e then CRecToken else CVar (elemToIntegral e)
fromAST' vars env (Pair e1 e2) = CPair (fromAST' vars env e1) (fromAST' vars env e2)
fromAST' vars env (Lambda sty e) = let env' = SCons sty env in
                                       CLambda [fromSing sty] (fromSing $ returnType env' e) (fromAST' vars env' e)
fromAST' vars env (App lam arg) = CApp (fromAST' vars env lam) (fromAST' vars env arg)
fromAST' vars env (Fix (Lambda ret e)) = fromAST' (vars + 1) (SCons ret env) e
fromAST' _ _ (Fix _) = error "Unsupported lambda reference in fix operator"
fromAST' _ _ (IntE n) = CIntE n
fromAST' _ _ (BoolE b) = CBoolE b
fromAST' _ _ UnitE = CUnitE

-- | Returns the list of free variable used in the expression.
freeVars :: CodegenAST -> [(LType, Int)]
freeVars = freeVars' 0 []

freeVars' :: Int -> [LType] -> CodegenAST -> [(LType, Int)]
freeVars' i types (CPrimBinaryOp _ e1 e2) = freeVars' i types e1 ++ freeVars' i types e2
freeVars' i types (CPrimUnaryOp _ e) = freeVars' i types e
freeVars' i types (CCond c e1 e2) = freeVars' i types c ++ freeVars' i types e1 ++ freeVars' i types e2
freeVars' i types (CVar v) = [(types !! v, v) | v >= i]
freeVars' i types (CPair e1 e2) = freeVars' i types e1 ++ freeVars' i types e2
freeVars' i types (CApp lam arg) = freeVars' i types lam ++ freeVars' i types arg
freeVars' i types (CLambda argsTy _ e) = freeVars' (i + length argsTy) (argsTy ++ types) e
freeVars' i types (CFix e) = freeVars' i types e
freeVars' _ _ _ = []

-- | Applies the closure conversion transformation to the expression.
closureConv :: CodegenAST -> CodegenAST
closureConv lam@(CLambda vs ret e) = let e' = closureConv e
                                         vars = freeVars lam in
                                         CLambda (map fst vars ++ vs) ret (e' `applyTo` map snd vars)
closureConv (CPrimUnaryOp op e) = CPrimUnaryOp op (closureConv e)
closureConv (CPrimBinaryOp op e1 e2) = CPrimBinaryOp op (closureConv e1) (closureConv e2)
closureConv (CCond c e1 e2) = CCond (closureConv c) (closureConv e1) (closureConv e2)
closureConv (CPair e1 e2) = CPair (closureConv e1) (closureConv e2)
closureConv (CApp lam arg) = CApp (closureConv lam) (closureConv arg)
closureConv (CFix e) = CFix (closureConv e)
closureConv e = e

applyTo :: CodegenAST -> [Int] -> CodegenAST
applyTo = foldl (\e a -> CApp e $ CVar a)

-- | Applies the lambda lifting transformation to the expression.
liftLam :: CodegenAST -> WriterT [Declaration] (State Int) CodegenAST
liftLam (CLambda vs ret e) = do
  fresh <- get
  put $ fresh + 1
  e' <- liftLam e
  tell $ pure $ Decl vs ret e'
  pure $ CCall fresh
liftLam (CPrimUnaryOp op e) = CPrimUnaryOp op <$> liftLam e
liftLam (CPrimBinaryOp op e1 e2) = CPrimBinaryOp op <$> liftLam e1 <*> liftLam e2
liftLam (CCond c e1 e2) = CCond <$> liftLam c <*> liftLam e1 <*> liftLam e2
liftLam (CPair e1 e2) = CPair <$> liftLam e1 <*> liftLam e2
liftLam (CApp lam arg) = CApp <$> liftLam lam <*> liftLam arg
liftLam (CFix lam) = liftLam lam
liftLam e = pure e

-- | Joins sequences of lambda abstractions in single multi-parameters lambda
-- abstractions.
smash :: CodegenAST -> CodegenAST
smash (CLambda vs _ (CLambda vs' ret' e)) = smash (CLambda (vs ++ vs') ret' e)
smash (CLambda vs ret e) = CLambda vs ret (smash e)
smash (CPrimBinaryOp op e1 e2) = CPrimBinaryOp op (smash e1) (smash e2)
smash (CPrimUnaryOp op e) = CPrimUnaryOp op (smash e)
smash (CCond c e1 e2) = CCond (smash c) (smash e1) (smash e2)
smash (CPair e1 e2) = CPair (smash e1) (smash e2)
smash (CApp lam arg) = CApp (smash lam) (smash arg)
smash e = e
