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

module Lab.Decls ( CodegenAST(..)
                 , Declaration(..)
                 , CodegenEnv(..)
                 , fromAST
                 , closureConv
                 , prettyCodegenAST
                 , liftLam
                 , smash
                 , freeVars) where

import Control.Monad.Writer
import Control.Monad.State
import Data.Kind
import Data.List.Extra
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal
import Data.Text.Prettyprint.Doc.Symbols.Unicode
import Data.Singletons
import Data.Singletons.Prelude

import Lab.Types
import Lab.Utils
import Lab.AST

data CodegenAST :: Type where
  CIntE  :: Integer -> CodegenAST
  CBoolE :: Bool -> CodegenAST
  CUnitE :: CodegenAST
  CPrimUnaryOp :: UnaryOp arg ret -> CodegenAST -> CodegenAST
  CPrimBinaryOp :: BinaryOp arg1 arg2 ret -> CodegenAST -> CodegenAST -> CodegenAST
  CCond :: CodegenAST -> CodegenAST -> CodegenAST -> CodegenAST
  CVar :: Int -> CodegenAST
  CPair :: CodegenAST -> CodegenAST -> CodegenAST
  CCall :: Int -> CodegenAST
  CLambda :: [LType] -> LType -> CodegenAST -> CodegenAST
  CApp :: CodegenAST -> CodegenAST -> CodegenAST
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

prettyCodegenAST :: CodegenAST -> Doc AnsiStyle
prettyCodegenAST = snd . go 0 initPrec
 where
  go :: Int -> Rational -> CodegenAST -> (Int, Doc AnsiStyle)
  go i _ (CIntE  n) = (i, annotate bold (pretty n))
  go i _ (CBoolE b) = (i, annotate bold (pretty b))
  go i _ CUnitE     = (i, annotate bold (pretty "unit"))
  go i prec (CPrimUnaryOp op e1) =
    (i, maybeParens (prec >= opPrec op) $ pretty op <> snd (go i (opPrecArg op) e1))
  go i prec (CPrimBinaryOp op e1 e2) =
    (i, maybeParens (prec >= binOpPrec op) $
          snd (go i (binOpLeftPrec op) e1)
          <+> pretty op
          <+> snd (go i (binOpRightPrec op) e2))
  go i prec (CCond c e1 e2) =
    (i, maybeParens (prec >= ifPrec) $ fillSep
      [ pretty "if"   <+> snd (go i initPrec c)
      , pretty "then" <+> snd (go i initPrec e1)
      , pretty "else" <+> snd (go i initPrec e2)
      ])
  go i _ (CVar v) = (i, colorVar v $ pretty '#' <> pretty v)
  go i _ (CCall v) = (i, pretty "call" <+> pretty v)
  go i prec (CLambda args _ e) = case go i initPrec e of
    (i_body, doc_body) ->
      (i_body + 1, maybeParens (prec >= lambdaPrec) $
        fillSep [ pretty 'λ' <+> pretty args <> pretty '.'
                , doc_body
                ])
  go i prec (CApp e arg) = (i, maybeParens (prec >= appPrec) $
    snd (go i appLeftPrec e) <+> snd (go i appRightPrec arg))
  go i _ (CPair f s) = (i, sGuillemetsOut $
    snd (go i initPrec f) <> comma <> snd (go i initPrec s))

  colors :: [Color]
  colors = cycle [Red, Green, Yellow, Blue, Magenta, Cyan]

  colorVar :: Int -> Doc AnsiStyle -> Doc AnsiStyle
  colorVar i = annotate (color $ colors !! i)

fromAST :: SList env -> AST env ty -> CodegenAST
fromAST _   (IntE n) = CIntE n
fromAST _   (BoolE b) = CBoolE b
fromAST _   UnitE = CUnitE
fromAST env (PrimUnaryOp op e) = CPrimUnaryOp op (fromAST env e)
fromAST env (PrimBinaryOp op e1 e2) = CPrimBinaryOp op (fromAST env e1) (fromAST env e2)
fromAST env (Cond c e1 e2) = CCond (fromAST env c) (fromAST env e1) (fromAST env e2)
fromAST _   (Var e) = CVar (elemToIntegral e)
fromAST env (Pair e1 e2) = CPair (fromAST env e1) (fromAST env e2)
fromAST _   (Fix _) = error "Fix operator is not implemented yet"
fromAST env (Lambda sty e) = CLambda [fromSing sty] (fromSing $ returnType (SCons sty env) e) (fromAST (SCons sty env) e)
fromAST env (App lam arg) = CApp (fromAST env lam) (fromAST env arg)

freeVars :: CodegenAST -> [(LType, Int)]
freeVars = go 0 []
  where go :: Int -> [LType] -> CodegenAST -> [(LType, Int)]
        go i types (CPrimBinaryOp _ e1 e2) = go i types e1 ++ go i types e2
        go i types (CPrimUnaryOp _ e) = go i types e
        go i types (CCond c e1 e2) = go i types c ++ go i types e1 ++ go i types e2
        go i types (CVar v) = [(types !! (v - 1), v) | v >= i]
        go i types (CPair e1 e2) = go i types e1 ++ go i types e2
        go i types (CApp lam arg) = go i types lam ++ go i types arg
        go i types (CLambda argsTy _ e) = go (i + length argsTy) (types ++ argsTy) e
        go _ _ _ = []

closureConv :: CodegenAST -> CodegenAST
closureConv lam@(CLambda vs ret e) = let e' = closureConv e
                                         vars = freeVars lam in
                                         CLambda (map fst vars ++ vs) ret (e' `applyTo` map snd vars)
closureConv (CPrimUnaryOp op e) = CPrimUnaryOp op (closureConv e)
closureConv (CPrimBinaryOp op e1 e2) = CPrimBinaryOp op (closureConv e1) (closureConv e2)
closureConv (CCond c e1 e2) = CCond (closureConv c) (closureConv e1) (closureConv e2)
closureConv (CPair e1 e2) = CPair (closureConv e1) (closureConv e2)
closureConv (CApp lam arg) = CApp (closureConv lam) (closureConv arg)
closureConv e = e

applyTo :: CodegenAST -> [Int] -> CodegenAST
applyTo = foldl (\e a -> CApp e $ CVar a)

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
liftLam e = pure e

smash :: CodegenAST -> CodegenAST
smash (CLambda vs _ (CLambda vs' ret' e)) = smash (CLambda (vs ++ vs') ret' e)
smash (CLambda vs ret e) = CLambda vs ret (smash e)
smash (CPrimBinaryOp op e1 e2) = CPrimBinaryOp op (smash e1) (smash e2)
smash (CPrimUnaryOp op e) = CPrimUnaryOp op (smash e)
smash (CCond c e1 e2) = CCond (smash c) (smash e1) (smash e2)
smash (CPair e1 e2) = CPair (smash e1) (smash e2)
smash (CApp lam arg) = CApp (smash lam) (smash arg)
smash e = e
