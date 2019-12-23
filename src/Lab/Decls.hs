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
  CFix :: CodegenAST -> CodegenAST
  CRecToken :: CodegenAST
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
  go i prec (CFix e) = (i, maybeParens (prec >= appPrec) $
    pretty "fix" <+> snd (go i initPrec e))
  go i _ CRecToken = (i, pretty "rec call")

  colors :: [Color]
  colors = cycle [Red, Green, Yellow, Blue, Magenta, Cyan]

  colorVar :: Int -> Doc AnsiStyle -> Doc AnsiStyle
  colorVar i = annotate (color $ colors !! i)

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
fromAST' _ _ (Fix _) = error "Unsupported"
fromAST' _ _ (IntE n) = CIntE n
fromAST' _ _ (BoolE b) = CBoolE b
fromAST' _ _ UnitE = CUnitE

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

smash :: CodegenAST -> CodegenAST
smash (CLambda vs _ (CLambda vs' ret' e)) = smash (CLambda (vs ++ vs') ret' e)
smash (CLambda vs ret e) = CLambda vs ret (smash e)
smash (CPrimBinaryOp op e1 e2) = CPrimBinaryOp op (smash e1) (smash e2)
smash (CPrimUnaryOp op e) = CPrimUnaryOp op (smash e)
smash (CCond c e1 e2) = CCond (smash c) (smash e1) (smash e2)
smash (CPair e1 e2) = CPair (smash e1) (smash e2)
smash (CApp lam arg) = CApp (smash lam) (smash arg)
smash e = e
