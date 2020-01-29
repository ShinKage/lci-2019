{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}

-------------------------------------------------------------------------------
-- |
-- Module      : Lab.Eval
-- Description : Evaluation and stepping functions.
-- Copyright   : (c) Giuseppe Lomurno, 2019
-- License     : ...
-- Maintainer  : Giuseppe Lomurno <g.lomurno@studenti.unipi.it>
-- Stability   : experimental
-- Portability : non-portable (?)
--
-------------------------------------------------------------------------------

module Lab.Eval where

import Data.Kind
import Data.List.Extra
import Data.Singletons.Prelude.List hiding (Elem, Length)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal

import Lab.AST
import Lab.Types

-- | Converts Lab types to Haskell types
type family Concrete (t :: LType) :: Type where
  Concrete LInt = Integer
  Concrete LBool = Bool
  Concrete LUnit = ()
  Concrete (LProduct ty1 ty2) = (Concrete ty1, Concrete ty2)
  Concrete (LArrow ty1 ty2) = AST '[] ty1 -> AST '[] ty2
  Concrete (LIO ty) = Concrete ty

-- | Lab value representation. Holds both the reduced AST combinator
-- and the corresponding Haskell raw value.
data Value :: LType -> Type where
  Value :: { ast :: AST '[] ty, val :: Concrete ty } -> Value ty

-- | Evaluation function for Lab.
interpret :: AST '[] a -> IO (Value a)
interpret (IOPure e) = do
  e' <- interpret e
  pure $ Value (IOPure $ ast e') (val e')
interpret (IOBind x f) = do
  IOPure x' <- ast <$> interpret x
  f' <- interpret f
  interpret $ val f' x'
interpret (IOPrimRead ty) = case ty of
  SLInt -> do
    n <- read <$> getLine
    pure $ Value (IOPure $ IntE n) n
  SLBool -> do
    b <- read <$> getLine
    pure $ Value (IOPure $ BoolE b) b
  SLUnit -> do
    u <- read <$> getLine
    pure $ Value (IOPure UnitE) u
  _ -> error "impossible match"
interpret e@(IntE  n) = pure $ Value e n
interpret e@(BoolE b) = pure $ Value e b
interpret UnitE       = pure $ Value UnitE ()
interpret (Cond c e1 e2) = do
  c' <- interpret c
  if val c' then interpret e1 else interpret e2
interpret (Var prf) = \case {} $ prf -- Empty case because an Elem instance is impossible with an empty context
interpret e@(Lambda _ body) = pure $ Value e (`subst` body)
interpret (App lam arg) = do
  lam' <- interpret lam
  interpret $ val lam' arg
interpret (Fix e) = do
  e' <- interpret e
  interpret $ unfix e (val e')
interpret (Pair f s) = do
  f' <- interpret f
  s' <- interpret s
  pure $ Value (Pair (ast f') (ast s')) (val f', val s')
interpret (PrimUnaryOp PrimNeg e) = do
  v <- negate . val <$> interpret e
  pure $ Value (IntE v) v
interpret (PrimUnaryOp PrimNot e) = do
  v <- not . val <$> interpret e
  pure $ Value (BoolE v) v
interpret (PrimUnaryOp PrimFst e) = interpret e >>= \case
  Value (Pair e' _) _ -> interpret e'
  _ -> error "impossible match"
interpret (PrimUnaryOp PrimSnd e) = interpret e >>= \case
  Value (Pair _ e') _ -> interpret e'
  _ -> error "impossible match"
interpret (PrimBinaryOp PrimAdd e1 e2) = do
  v1 <- val <$> interpret e1
  v2 <- val <$> interpret e2
  let v = v1 + v2
  pure $ Value (IntE v) v
interpret (PrimBinaryOp PrimSub e1 e2) = do
  v1 <- val <$> interpret e1
  v2 <- val <$> interpret e2
  let v = v1 - v2
  pure $ Value (IntE v) v
interpret (PrimBinaryOp PrimMul e1 e2) = do
  v1 <- val <$> interpret e1
  v2 <- val <$> interpret e2
  let v = v1 * v2
  pure $ Value (IntE v) v
interpret (PrimBinaryOp PrimDiv e1 e2) = do
  v1 <- val <$> interpret e1
  v2 <- val <$> interpret e2
  let v = v1 `div` v2
  pure $ Value (IntE v) v
interpret (PrimBinaryOp PrimAnd e1 e2) = do
  v1 <- val <$> interpret e1
  v2 <- val <$> interpret e2
  let v = v1 && v2
  pure $ Value (BoolE v) v
interpret (PrimBinaryOp PrimOr e1 e2) = do
  v1 <- val <$> interpret e1
  v2 <- val <$> interpret e2
  let v = v1 || v2
  pure $ Value (BoolE v) v
interpret (PrimBinaryOp PrimLT e1 e2) = do
  v1 <- val <$> interpret e1
  v2 <- val <$> interpret e2
  let v = v1 < v2
  pure $ Value (BoolE v) v
interpret (PrimBinaryOp PrimGT e1 e2) = do
  v1 <- val <$> interpret e1
  v2 <- val <$> interpret e2
  let v = v1 > v2
  pure $ Value (BoolE v) v
interpret (PrimBinaryOp PrimLE e1 e2) = do
  v1 <- val <$> interpret e1
  v2 <- val <$> interpret e2
  let v = v1 <= v2
  pure $ Value (BoolE v) v
interpret (PrimBinaryOp PrimGE e1 e2) = do
  v1 <- val <$> interpret e1
  v2 <- val <$> interpret e2
  let v = v1 >= v2
  pure $ Value (BoolE v) v
interpret (PrimBinaryOp PrimEq e1 e2) = do
  e1' <- ast <$> interpret e1
  e2' <- ast <$> interpret e2
  case (e1', e2') of
    (IntE  n, IntE  m) -> pure $ Value (BoolE $ n == m) (n == m)
    (BoolE n, BoolE m) -> pure $ Value (BoolE $ n == m) (n == m)
    (UnitE, UnitE) -> pure $ Value (BoolE True) True
    (_, _) -> error "impossible match"
interpret (PrimBinaryOp PrimNeq e1 e2) = do
  e1' <- ast <$> interpret e1
  e2' <- ast <$> interpret e2
  case (e1', e2') of
    (IntE  n, IntE  m) -> pure $ Value (BoolE $ n /= m) (n /= m)
    (BoolE n, BoolE m) -> pure $ Value (BoolE $ n /= m) (n /= m)
    (UnitE, UnitE) -> pure $ Value (BoolE False) False
    (_, _) -> error "impossible match"

-- | Evaluation function for Lab.
eval :: AST '[] a -> Value a
eval e@(IntE  n) = Value e n
eval e@(BoolE b) = Value e b
eval e@UnitE     = Value e ()
eval (Cond c e1 e2) = if val (eval c) then eval e1 else eval e2
eval (Var idx) = \case {} $ idx -- Empty case because an Elem instance is impossible with an empty context
eval e@(Lambda _ body) = Value e (`subst` body)
eval (App lam arg) = eval $ val (eval lam) arg
eval (Fix e) = eval $ unfix e (val $ eval e)
eval (Pair f s) = let f' = eval f
                      s' = eval s in
                      Value (Pair (ast f') (ast s')) (val f', val s')
eval (PrimUnaryOp PrimNeg e) = let v = negate $ val $ eval e in Value (IntE v) v
eval (PrimUnaryOp PrimNot e) = let v = not $ val $ eval e in Value (BoolE v) v
eval (PrimUnaryOp PrimFst e) = case eval e of
  Value (Pair e' _) _ -> eval e'
  _ -> error "impossible match"
eval (PrimUnaryOp PrimSnd e) = case eval e of
  Value (Pair _ e') _ -> eval e'
  _ -> error "impossible match"
eval (PrimBinaryOp PrimAdd e1 e2) =
  let v1 = val $ eval e1
      v2 = val $ eval e2
      v  = v1 + v2
  in  Value (IntE v) v
eval (PrimBinaryOp PrimSub e1 e2) =
  let v1 = val $ eval e1
      v2 = val $ eval e2
      v  = v1 - v2
  in  Value (IntE v) v
eval (PrimBinaryOp PrimMul e1 e2) =
  let v1 = val $ eval e1
      v2 = val $ eval e2
      v  = v1 * v2
  in  Value (IntE v) v
eval (PrimBinaryOp PrimDiv e1 e2) =
  let v1 = val $ eval e1
      v2 = val $ eval e2
      v  = v1 `div` v2
  in  Value (IntE v) v
eval (PrimBinaryOp PrimAnd e1 e2) =
  let v1 = val $ eval e1
      v2 = val $ eval e2
      v  = v1 && v2
  in  Value (BoolE v) v
eval (PrimBinaryOp PrimOr e1 e2) =
  let v1 = val $ eval e1
      v2 = val $ eval e2
      v  = v1 || v2
  in  Value (BoolE v) v
eval (PrimBinaryOp PrimLT e1 e2) =
  let v1 = val $ eval e1
      v2 = val $ eval e2
      v  = v1 < v2
  in  Value (BoolE v) v
eval (PrimBinaryOp PrimGT e1 e2) =
  let v1 = val $ eval e1
      v2 = val $ eval e2
      v  = v1 > v2
  in  Value (BoolE v) v
eval (PrimBinaryOp PrimLE e1 e2) =
  let v1 = val $ eval e1
      v2 = val $ eval e2
      v  = v1 <= v2
  in  Value (BoolE v) v
eval (PrimBinaryOp PrimGE e1 e2) =
  let v1 = val $ eval e1
      v2 = val $ eval e2
      v  = v1 >= v2
  in  Value (BoolE v) v
eval (PrimBinaryOp PrimEq e1 e2) = case (ast (eval e1), ast (eval e2)) of
  (IntE  n, IntE m ) -> Value (BoolE $ n == m) (n == m)
  (BoolE n, BoolE m) -> Value (BoolE $ n == m) (n == m)
  (UnitE, UnitE) -> Value (BoolE True) True
  -- If we explicitly pattern match on conflicting cases, Haskell recognizes the conflicting constraint
  -- but we have not found yet, a way to generate an absurd value.
  (_, _) -> error "impossible match"
eval (PrimBinaryOp PrimNeq e1 e2) = case (ast (eval e1), ast (eval e2)) of
  (IntE  n, IntE m ) -> Value (BoolE $ n /= m) (n /= m)
  (BoolE n, BoolE m) -> Value (BoolE $ n /= m) (n /= m)
  (UnitE, UnitE) -> Value (BoolE False) False
  -- If we explicitly pattern match on conflicting cases, Haskell recognizes the conflicting constraint
  -- but we have not found yet, a way to generate an absurd value.
  (_, _) -> error "impossible match"
eval (IOPure _) = error "IO operation not supported in regular evaluation"
eval (IOBind _ _) = error "IO operation not supported in regular evaluation"
eval (IOPrimRead _) = error "IO operation not supported in regular evaluation"

-- | Term substitution.
subst :: forall env sub ret. AST env sub -> AST (sub : env) ret -> AST env ret
subst e = go LZ
  where go :: Length (locals :: [LType])
           -> AST (locals ++ sub : env) ty
           -> AST (locals ++ env) ty
        go _ (IntE n)                  = IntE n
        go _ (BoolE b)                 = BoolE b
        go _ UnitE                     = UnitE
        go len (Lambda ty body)        = Lambda ty (go (LS len) body)
        go len (Var v)                 = substVar len v
        go len (App body arg)          = App (go len body) (go len arg)
        go len (Fix body)              = Fix (go len body)
        go len (Cond c e1 e2)          = Cond (go len c) (go len e1) (go len e2)
        go len (Pair e1 e2)            = Pair (go len e1) (go len e2)
        go len (PrimUnaryOp op e1)     = PrimUnaryOp op (go len e1)
        go len (PrimBinaryOp op e1 e2) = PrimBinaryOp op (go len e1) (go len e2)
        go len (IOPure a) = IOPure (go len a)
        go len (IOBind x f) = IOBind (go len x) (go len f)
        go _ (IOPrimRead x) = IOPrimRead x

        substVar :: Length (locals :: [LType])
                 -> Elem (locals ++ sub : env) ty
                 -> AST (locals ++ env) ty
        substVar LZ Here            = e
        substVar LZ (There v)       = Var v
        substVar (LS _) Here        = Var Here
        substVar (LS len) (There v) = shift $ substVar len v


-- | Shifting for variable substitution.
shift :: AST env ty -> AST (t : env) ty
shift = shifts $ LS LZ

shifts :: forall prefix env ty. Length prefix
       -> AST env ty
       -> AST (prefix ++ env) ty
shifts prefix = go LZ
  where go :: Length (locals :: [LType])
           -> AST (locals ++ env) t
           -> AST (locals ++ prefix ++ env) t
        go _   (IntE n)                  = IntE n
        go _   (BoolE b)                 = BoolE b
        go _   UnitE                     = UnitE
        go len (Lambda ty body)          = Lambda ty (go (LS len) body)
        go len (Var v)                   = Var (shiftsVar len v)
        go len (App body arg)            = App (go len body) (go len arg)
        go len (Fix body)                = Fix (go len body)
        go len (Cond c e1 e2)            = Cond (go len c) (go len e1) (go len e2)
        go len (Pair e1 e2)              = Pair (go len e1) (go len e2)
        go len (PrimBinaryOp op lhs rhs) = PrimBinaryOp op (go len lhs) (go len rhs)
        go len (PrimUnaryOp op arg)      = PrimUnaryOp op (go len arg)
        go len (IOPure e) = IOPure (go len e)
        go len (IOBind x f) = IOBind (go len x) (go len f)
        go _ (IOPrimRead x) = IOPrimRead x

        shiftsVar :: Length (locals :: [LType])
                  -> Elem (locals ++ env) t
                  -> Elem (locals ++ prefix ++ env) t
        shiftsVar LZ     v         = weakenElem prefix v
        shiftsVar (LS _) Here      = Here
        shiftsVar (LS l) (There e) = There $ shiftsVar l e

unfix :: AST '[] (LArrow a a) -> Concrete (LArrow a a) -> AST '[] a
unfix lam v = v $ Fix lam

-- | Stepped evaluation, can be either an AST that still needs evaluation or a value.
data Step :: LType -> Type where
  StepAST :: AST '[] a -> Step a
  StepValue :: Value a -> Step a

prettyStep :: Step a -> Doc AnsiStyle
prettyStep (StepAST e) = prettyAST e
prettyStep (StepValue v) = prettyAST (ast v)

-- | Performs a single step of beta-reduction for a Lab expression.
step :: AST '[] a -> Step a
step e@(IntE  n) = StepValue $ Value e n
step e@(BoolE b) = StepValue $ Value e b
step UnitE       = StepValue $ Value UnitE ()
step (Cond c e1 e2) = case step c of
  StepAST c'   -> StepAST $ Cond c' e1 e2
  StepValue c' -> StepAST $ if val c' then e1 else e2
step (Var idx) = \case {} $ idx -- Empty case because an Elem instance is impossible with an empty context
step e@(Lambda _ body) = StepValue $ Value e (`subst` body)
step (App lam arg) = case step lam of
  StepAST lam'   -> StepAST $ App lam' arg
  StepValue lam' -> StepAST $ val lam' arg
step (Fix e) = case step e of
  StepAST e'   -> StepAST $ Fix e'
  StepValue e' -> StepAST $ unfix (ast e') (val e')
step (Pair f s) = case step f of
  StepAST f'   -> StepAST $ Pair f' s
  StepValue f' -> case step s of
    StepAST s'   -> StepAST $ Pair (ast f') s'
    StepValue s' -> StepValue $ Value (Pair (ast f') (ast s')) (val f', val s')
step (PrimUnaryOp PrimNeg e) = case step e of
  StepAST e'   -> StepAST $ PrimUnaryOp PrimNeg e'
  StepValue e' -> let v = negate $ val e' in StepValue $ Value (IntE v) v
step (PrimUnaryOp PrimNot e) = case step e of
  StepAST e'   -> StepAST $ PrimUnaryOp PrimNot e'
  StepValue e' -> let v = not $ val e' in StepValue $ Value (BoolE v) v
step (PrimUnaryOp PrimFst e) = case step e of
  StepAST e'                      -> StepAST $ PrimUnaryOp PrimFst e'
  StepValue (Value (Pair e' _) _) -> StepAST e'
  _ -> error "impossible match"
step (PrimUnaryOp PrimSnd e) = case step e of
  StepAST e'                      -> StepAST $ PrimUnaryOp PrimSnd e'
  StepValue (Value (Pair _ e') _) -> StepAST e'
  _ -> error "impossible match"
step (PrimBinaryOp PrimAdd e1 e2) = case step e1 of
  StepAST e1'   -> StepAST $ PrimBinaryOp PrimAdd e1' e2
  StepValue e1' -> case step e2 of
    StepAST e2'   -> StepAST $ PrimBinaryOp PrimAdd (ast e1') e2'
    StepValue e2' -> let v = val e1' + val e2' in StepValue $ Value (IntE v) v
step (PrimBinaryOp PrimSub e1 e2) = case step e1 of
  StepAST e1'   -> StepAST $ PrimBinaryOp PrimSub e1' e2
  StepValue e1' -> case step e2 of
    StepAST e2'   -> StepAST $ PrimBinaryOp PrimSub (ast e1') e2'
    StepValue e2' -> let v = val e1' - val e2' in StepValue $ Value (IntE v) v
step (PrimBinaryOp PrimMul e1 e2) = case step e1 of
  StepAST e1'   -> StepAST $ PrimBinaryOp PrimMul e1' e2
  StepValue e1' -> case step e2 of
    StepAST e2'   -> StepAST $ PrimBinaryOp PrimMul (ast e1') e2'
    StepValue e2' -> let v = val e1' * val e2' in StepValue $ Value (IntE v) v
step (PrimBinaryOp PrimDiv e1 e2) = case step e1 of
  StepAST e1'   -> StepAST $ PrimBinaryOp PrimDiv e1' e2
  StepValue e1' -> case step e2 of
    StepAST e2'   -> StepAST $ PrimBinaryOp PrimDiv (ast e1') e2'
    StepValue e2' -> let v = val e1' `div` val e2' in StepValue $ Value (IntE v) v
step (PrimBinaryOp PrimAnd e1 e2) = case step e1 of
  StepAST e1'   -> StepAST $ PrimBinaryOp PrimAnd e1' e2
  StepValue e1' -> case step e2 of
    StepAST e2'   -> StepAST $ PrimBinaryOp PrimAnd (ast e1') e2'
    StepValue e2' -> let v = val e1' && val e2' in StepValue $ Value (BoolE v) v
step (PrimBinaryOp PrimOr e1 e2) = case step e1 of
  StepAST e1'   -> StepAST $ PrimBinaryOp PrimOr e1' e2
  StepValue e1' -> case step e2 of
    StepAST e2'   -> StepAST $ PrimBinaryOp PrimOr (ast e1') e2'
    StepValue e2' -> let v = val e1' || val e2' in StepValue $ Value (BoolE v) v
step (PrimBinaryOp PrimLT e1 e2) = case step e1 of
  StepAST e1'   -> StepAST $ PrimBinaryOp PrimLT e1' e2
  StepValue e1' -> case step e2 of
    StepAST e2'   -> StepAST $ PrimBinaryOp PrimLT (ast e1') e2'
    StepValue e2' -> let v = val e1' < val e2' in StepValue $ Value (BoolE v) v
step (PrimBinaryOp PrimGT e1 e2) = case step e1 of
  StepAST e1'   -> StepAST $ PrimBinaryOp PrimGT e1' e2
  StepValue e1' -> case step e2 of
    StepAST e2'   -> StepAST $ PrimBinaryOp PrimGT (ast e1') e2'
    StepValue e2' -> let v = val e1' > val e2' in StepValue $ Value (BoolE v) v
step (PrimBinaryOp PrimLE e1 e2) = case step e1 of
  StepAST e1'   -> StepAST $ PrimBinaryOp PrimLE e1' e2
  StepValue e1' -> case step e2 of
    StepAST e2'   -> StepAST $ PrimBinaryOp PrimLE (ast e1') e2'
    StepValue e2' -> let v = val e1' <= val e2' in StepValue $ Value (BoolE v) v
step (PrimBinaryOp PrimGE e1 e2) = case step e1 of
  StepAST e1'   -> StepAST $ PrimBinaryOp PrimGE e1' e2
  StepValue e1' -> case step e2 of
    StepAST e2'   -> StepAST $ PrimBinaryOp PrimGE (ast e1') e2'
    StepValue e2' -> let v = val e1' >= val e2' in StepValue $ Value (BoolE v) v
step (PrimBinaryOp PrimEq e1 e2) = case step e1 of
  StepAST e1'   -> StepAST $ PrimBinaryOp PrimEq e1' e2
  StepValue e1' -> case step e2 of
    StepAST e2'   -> StepAST $ PrimBinaryOp PrimEq (ast e1') e2'
    StepValue e2' -> case (ast e1', ast e2') of
      (IntE n, IntE m)   -> let v = n == m in StepValue $ Value (BoolE v) v
      (BoolE n, BoolE m) -> let v = n == m in StepValue $ Value (BoolE v) v
      (UnitE, UnitE)     -> StepValue $ Value (BoolE True) True
      -- If we explicitly pattern match on conflicting cases, Haskell recognizes the conflicting constraint
      -- but we have not found yet, a way to generate an absurd value.
      _ -> error "impossible match"
step (PrimBinaryOp PrimNeq e1 e2) = case step e1 of
  StepAST e1'   -> StepAST $ PrimBinaryOp PrimNeq e1' e2
  StepValue e1' -> case step e2 of
    StepAST e2'   -> StepAST $ PrimBinaryOp PrimNeq (ast e1') e2'
    StepValue e2' -> case (ast e1', ast e2') of
      (IntE n, IntE m)   -> let v = n /= m in StepValue $ Value (BoolE v) v
      (BoolE n, BoolE m) -> let v = n /= m in StepValue $ Value (BoolE v) v
      (UnitE, UnitE)     -> StepValue $ Value (BoolE False) False
      -- If we explicitly pattern match on conflicting cases, Haskell recognizes the conflicting constraint
      -- but we have not found yet, a way to generate an absurd value.
      _ -> error "impossible match"
step (IOPure _) = error "IO operation not supported in regular evaluation"
step (IOBind _ _) = error "IO operation not supported in regular evaluation"
step (IOPrimRead _) = error "IO operation not supported in regular evaluation"

-- | Evaluation function for Lab.
interpretStep :: AST '[] a -> IO (Step a)
interpretStep (IOPure e) = interpretStep e >>= \case
  StepAST e' -> pure $ StepAST (IOPure e')
  StepValue e' -> pure $ StepValue $ Value (IOPure $ ast e') (val e')
interpretStep (IOBind x f) = interpretStep x >>= \case
  StepAST x' -> pure $ StepAST (IOBind x' f)
  StepValue x' -> interpretStep f >>= \case
    StepAST f' -> pure $ StepAST (IOBind (ast x') f')
    StepValue f' -> case ast x' of
      IOPure x'' -> pure $ StepAST (val f' x'')
      _ -> error "impossible match"
interpretStep (IOPrimRead ty) = case ty of
  SLInt -> do
    n <- read <$> getLine
    pure $ StepValue $ Value (IOPure $ IntE n) n
  SLBool -> do
    b <- read <$> getLine
    pure $ StepValue $ Value (IOPure $ BoolE b) b
  SLUnit -> do
    u <- read <$> getLine
    pure $ StepValue $ Value (IOPure UnitE) u
  _ -> error "impossible match"
interpretStep e@(IntE  n)    = pure $ StepValue (Value e n)
interpretStep e@(BoolE b)    = pure $ StepValue (Value e b)
interpretStep UnitE          = pure $ StepValue (Value UnitE ())
interpretStep (Cond c e1 e2) = interpretStep c >>= \case
  StepAST c'   -> pure $ StepAST (Cond c' e1 e2)
  StepValue c' -> pure $ StepAST (if val c' then e1 else e2)
interpretStep (Var prf) = \case {} $ prf -- Empty case because an Elem instance is impossible with an empty context
interpretStep e@(Lambda _ body) = pure $ StepValue (Value e (`subst` body))
interpretStep (App lam arg) = interpretStep lam >>= \case
  StepAST lam'   -> pure $ StepAST (App lam' arg)
  StepValue lam' -> pure $ StepAST (val lam' arg)
interpretStep (Fix e) = interpretStep e >>= \case
  StepAST e'   -> pure $ StepAST (Fix e')
  StepValue e' -> pure $ StepAST $ unfix (ast e') (val e')
interpretStep (Pair f s) = interpretStep f >>= \case
  StepAST f' -> pure $ StepAST (Pair f' s)
  StepValue f' -> interpretStep s >>= \case
    StepAST s' -> pure $ StepAST (Pair (ast f') s')
    StepValue s' -> pure $ StepValue $ Value (Pair (ast f') (ast s')) (val f', val s')
interpretStep (PrimUnaryOp PrimNeg e) = interpretStep e >>= \case
  StepAST e' -> pure $ StepAST (PrimUnaryOp PrimNeg e')
  StepValue e' -> let v = negate $ val e' in pure $ StepValue $ Value (IntE v) v
interpretStep (PrimUnaryOp PrimNot e) = interpretStep e >>= \case
  StepAST e' -> pure $ StepAST (PrimUnaryOp PrimNot e')
  StepValue e' -> let v = not $ val e' in pure $ StepValue $ Value (BoolE v) v
interpretStep (PrimUnaryOp PrimFst e) = interpretStep e >>= \case
  StepAST e' -> pure $ StepAST (PrimUnaryOp PrimFst e')
  StepValue (Value (Pair e' _) _) -> pure $ StepAST e'
  _ -> error "impossible match"
interpretStep (PrimUnaryOp PrimSnd e) = interpretStep e >>= \case
  StepAST e' -> pure $ StepAST (PrimUnaryOp PrimSnd e')
  StepValue (Value (Pair _ e') _) -> pure $ StepAST e'
  _ -> error "impossible match"
interpretStep (PrimBinaryOp PrimAdd e1 e2) = interpretStep e1 >>= \case
  StepAST e1' -> pure $ StepAST (PrimBinaryOp PrimAdd e1' e2)
  StepValue e1' -> interpretStep e2 >>= \case
    StepAST e2' -> pure $ StepAST (PrimBinaryOp PrimAdd (ast e1') e2')
    StepValue e2' -> let v = val e1' + val e2' in pure $ StepValue $ Value (IntE v) v
interpretStep (PrimBinaryOp PrimSub e1 e2) = interpretStep e1 >>= \case
  StepAST e1' -> pure $ StepAST (PrimBinaryOp PrimSub e1' e2)
  StepValue e1' -> interpretStep e2 >>= \case
    StepAST e2' -> pure $ StepAST (PrimBinaryOp PrimSub (ast e1') e2')
    StepValue e2' -> let v = val e1' - val e2' in pure $ StepValue $ Value (IntE v) v
interpretStep (PrimBinaryOp PrimMul e1 e2) = interpretStep e1 >>= \case
  StepAST e1' -> pure $ StepAST (PrimBinaryOp PrimMul e1' e2)
  StepValue e1' -> interpretStep e2 >>= \case
    StepAST e2' -> pure $ StepAST (PrimBinaryOp PrimMul (ast e1') e2')
    StepValue e2' -> let v = val e1' * val e2' in pure $ StepValue $ Value (IntE v) v
interpretStep (PrimBinaryOp PrimDiv e1 e2) = interpretStep e1 >>= \case
  StepAST e1' -> pure $ StepAST (PrimBinaryOp PrimDiv e1' e2)
  StepValue e1' -> interpretStep e2 >>= \case
    StepAST e2' -> pure $ StepAST (PrimBinaryOp PrimDiv (ast e1') e2')
    StepValue e2' -> let v = val e1' `div` val e2' in pure $ StepValue $ Value (IntE v) v
interpretStep (PrimBinaryOp PrimAnd e1 e2) = interpretStep e1 >>= \case
  StepAST e1' -> pure $ StepAST (PrimBinaryOp PrimAnd e1' e2)
  StepValue e1' -> interpretStep e2 >>= \case
    StepAST e2' -> pure $ StepAST (PrimBinaryOp PrimAnd (ast e1') e2')
    StepValue e2' -> let v = val e1' && val e2' in pure $ StepValue $ Value (BoolE v) v
interpretStep (PrimBinaryOp PrimOr e1 e2) = interpretStep e1 >>= \case
  StepAST e1' -> pure $ StepAST (PrimBinaryOp PrimOr e1' e2)
  StepValue e1' -> interpretStep e2 >>= \case
    StepAST e2' -> pure $ StepAST (PrimBinaryOp PrimOr (ast e1') e2')
    StepValue e2' -> let v = val e1' || val e2' in pure $ StepValue $ Value (BoolE v) v
interpretStep (PrimBinaryOp PrimLT e1 e2) = interpretStep e1 >>= \case
  StepAST e1' -> pure $ StepAST (PrimBinaryOp PrimLT e1' e2)
  StepValue e1' -> interpretStep e2 >>= \case
    StepAST e2' -> pure $ StepAST (PrimBinaryOp PrimLT (ast e1') e2')
    StepValue e2' -> let v = val e1' < val e2' in pure $ StepValue $ Value (BoolE v) v
interpretStep (PrimBinaryOp PrimGT e1 e2) = interpretStep e1 >>= \case
  StepAST e1' -> pure $ StepAST (PrimBinaryOp PrimGT e1' e2)
  StepValue e1' -> interpretStep e2 >>= \case
    StepAST e2' -> pure $ StepAST (PrimBinaryOp PrimGT (ast e1') e2')
    StepValue e2' -> let v = val e1' > val e2' in pure $ StepValue $ Value (BoolE v) v
interpretStep (PrimBinaryOp PrimLE e1 e2) = interpretStep e1 >>= \case
  StepAST e1' -> pure $ StepAST (PrimBinaryOp PrimLE e1' e2)
  StepValue e1' -> interpretStep e2 >>= \case
    StepAST e2' -> pure $ StepAST (PrimBinaryOp PrimLE (ast e1') e2')
    StepValue e2' -> let v = val e1' <= val e2' in pure $ StepValue $ Value (BoolE v) v
interpretStep (PrimBinaryOp PrimGE e1 e2) = interpretStep e1 >>= \case
  StepAST e1' -> pure $ StepAST (PrimBinaryOp PrimGE e1' e2)
  StepValue e1' -> interpretStep e2 >>= \case
    StepAST e2' -> pure $ StepAST (PrimBinaryOp PrimGE (ast e1') e2')
    StepValue e2' -> let v = val e1' >= val e2' in pure $ StepValue $ Value (BoolE v) v
interpretStep (PrimBinaryOp PrimEq e1 e2) = interpretStep e1 >>= \case
  StepAST e1' -> pure $ StepAST (PrimBinaryOp PrimEq e1' e2)
  StepValue e1' -> interpretStep e2 >>= \case
    StepAST e2' -> pure $ StepAST (PrimBinaryOp PrimEq (ast e1') e2')
    StepValue e2' -> case (ast e1', ast e2') of
      (IntE n, IntE m) -> let v = n == m in pure $ StepValue $ Value (BoolE v) v
      (BoolE n, BoolE m) -> let v = n == m in pure $ StepValue $ Value (BoolE v) v
      (UnitE, UnitE) -> pure $ StepValue $ Value (BoolE True) True
      -- If we explicitly pattern match on conflicting cases, Haskell recognizes the conflicting constraint
      -- but we have not found yet, a way to generate an absurd value.
      _ -> error "impossible match"
interpretStep (PrimBinaryOp PrimNeq e1 e2) = interpretStep e1 >>= \case
  StepAST e1' -> pure $ StepAST (PrimBinaryOp PrimNeq e1' e2)
  StepValue e1' -> interpretStep e2 >>= \case
    StepAST e2' -> pure $ StepAST (PrimBinaryOp PrimNeq (ast e1') e2')
    StepValue e2' -> case (ast e1', ast e2') of
      (IntE n, IntE m) -> let v = n /= m in pure $ StepValue $ Value (BoolE v) v
      (BoolE n, BoolE m) -> let v = n /= m in pure $ StepValue $ Value (BoolE v) v
      (UnitE, UnitE) -> pure $ StepValue $ Value (BoolE False) False
      -- If we explicitly pattern match on conflicting cases, Haskell recognizes the conflicting constraint
      -- but we have not found yet, a way to generate an absurd value.
      _ -> error "impossible match"
