{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}

-------------------------------------------------------------------------------
-- |
-- Module      : Lab.Eval
-- Description : Evaluation and stepping functions
-- Copyright   : (c) Giuseppe Lomurno, 2019
-- License     : ...
-- Maintainer  : Giuseppe Lomurno <g.lomurno@studenti.unipi.it>
-- Stability   : experimental
-- Portability : non-portable (?)
--
-------------------------------------------------------------------------------

module Lab.Eval (Value(..), Step(..), eval, step, prettyStep) where

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal
import Data.Kind
import Data.List.Extra
import Data.Singletons.Prelude.List hiding (Elem, Length)

import Lab.AST
import Lab.Types

-- | Converts Lab types to Haskell types
type family Concrete (t :: LType) :: Type where
  Concrete LInt = Integer
  Concrete LBool = Bool
  Concrete LUnit = ()
  Concrete (LProduct ty1 ty2) = (Concrete ty1, Concrete ty2)
  Concrete (LArrow ty1 ty2) = AST '[] ty1 -> AST '[] ty2

-- | Lab value representation. Holds both the reduced AST and the corresponding
-- Haskell raw value.
data Value :: LType -> Type where
  Value :: { expr :: AST '[] ty
           , val  :: Concrete ty
           } -> Value ty

-- | Evaluation function for Lab.
eval :: AST '[] a -> Value a
eval e@(IntE  n)    = Value e n
eval e@(BoolE b)    = Value e b
eval UnitE          = Value UnitE ()
eval (Cond c e1 e2) = if val (eval c) then eval e1 else eval e2
eval (Var prf) = \case {} $ prf -- Empty case because an Elem instance is impossible with an empty context
eval e@(Lambda _ body) = Value e (`subst` body)
eval (App lam arg) = eval $ val (eval lam) arg
eval (Fix e) = eval $ unfix e (val $ eval e)
eval (Pair f s) = let f' = eval f
                      s' = eval s in
                      Value (Pair (expr f') (expr s')) (val f', val s')
eval (PrimUnaryOp PrimNeg e) =
  let v = negate $ val $ eval e in Value (IntE v) v
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
eval (PrimBinaryOp PrimEq e1 e2) = case (expr (eval e1), expr (eval e2)) of
  (IntE  n, IntE m ) -> Value (BoolE $ n == m) (n == m)
  (BoolE n, BoolE m) -> Value (BoolE $ n == m) (n == m)
  (UnitE, UnitE) -> Value (BoolE True) True
  -- If we explicitly pattern match on conflicting cases, Haskell recognizes the conflicting constraint
  -- but we have not found yet, a way to generate an absurd value.
  (_, _) -> error "impossible match"
eval (PrimBinaryOp PrimNeq e1 e2) = case (expr (eval e1), expr (eval e2)) of
  (IntE  n, IntE m ) -> Value (BoolE $ n /= m) (n /= m)
  (BoolE n, BoolE m) -> Value (BoolE $ n /= m) (n /= m)
  (UnitE, UnitE) -> Value (BoolE False) False
  -- If we explicitly pattern match on conflicting cases, Haskell recognizes the conflicting constraint
  -- but we have not found yet, a way to generate an absurd value.
  (_, _) -> error "impossible match"

-- | Term substitution.
subst :: forall env sub ret. AST env sub -> AST (sub : env) ret -> AST env ret
subst e = go LZ
  where go :: Length (locals :: [LType])
           -> AST (locals ++ sub : env) ty
           -> AST (locals ++ env) ty
        go _ (IntE n) = IntE n
        go _ (BoolE b) = BoolE b
        go _ UnitE = UnitE
        go len (Lambda ty body) = Lambda ty (go (LS len) body)
        go len (Var v) = substVar len v
        go len (App body arg) = App (go len body) (go len arg)
        go len (Fix body) = Fix (go len body)
        go len (Cond c e1 e2) = Cond (go len c) (go len e1) (go len e2)
        go len (Pair e1 e2) = Pair (go len e1) (go len e2)
        go len (PrimUnaryOp op e1) = PrimUnaryOp op (go len e1)
        go len (PrimBinaryOp op e1 e2) = PrimBinaryOp op (go len e1) (go len e2)

        substVar :: Length (locals :: [LType])
                 -> Elem (locals ++ sub : env) ty
                 -> AST (locals ++ env) ty
        substVar LZ Here = e
        substVar LZ (There v) = Var v
        substVar (LS _) Here = Var Here
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

        shiftsVar :: Length (locals :: [LType])
                  -> Elem (locals ++ env) t
                  -> Elem (locals ++ prefix ++ env) t
        shiftsVar LZ     v         = weakenElem prefix v
        shiftsVar (LS _) Here      = Here
        shiftsVar (LS l) (There e) = There $ shiftsVar l e

unfix :: AST '[] (LArrow a a) -> Concrete (LArrow a a) -> AST '[] a
unfix lam v = v $ Fix lam

data Step :: LType -> Type where
  StepAST :: AST '[] a -> Step a
  StepValue :: Value a -> Step a

prettyStep :: Step a -> Doc AnsiStyle
prettyStep (StepAST ast) = prettyAST ast
prettyStep (StepValue v) = prettyAST (expr v)

-- | Evaluation function for Lab.
step :: AST '[] a -> Step a
step e@(IntE  n)    = StepValue (Value e n)
step e@(BoolE b)    = StepValue (Value e b)
step UnitE          = StepValue (Value UnitE ())
step (Cond c e1 e2) = case step c of
  StepAST c'   -> StepAST (Cond c' e1 e2)
  StepValue c' -> StepAST (if val c' then e1 else e2)
step (Var prf) = \case {} $ prf -- Empty case because an Elem instance is impossible with an empty context
step e@(Lambda _ body) = StepValue (Value e (`subst` body))
step (App lam arg) = case step lam of
  StepAST lam'   -> StepAST (App lam' arg)
  StepValue lam' -> case step arg of
    StepAST arg'   -> StepAST (App (expr lam') arg')
    StepValue arg' -> StepAST (val lam' $ expr arg')
step (Fix e) = case step e of
  StepAST e'   -> StepAST (Fix e')
  StepValue e' -> StepAST $ unfix (expr e') (val e')
step (Pair f s) = case step f of
  StepAST f' -> StepAST (Pair f' s)
  StepValue f' -> case step s of
    StepAST s' -> StepAST (Pair (expr f') s')
    StepValue s' -> StepValue $ Value (Pair (expr f') (expr s')) (val f', val s')
step (PrimUnaryOp PrimNeg e) = case step e of
  StepAST e' -> StepAST (PrimUnaryOp PrimNeg e')
  StepValue e' -> let v = negate $ val e' in StepValue $ Value (IntE v) v
step (PrimUnaryOp PrimNot e) = case step e of
  StepAST e' -> StepAST (PrimUnaryOp PrimNot e')
  StepValue e' -> let v = not $ val e' in StepValue $ Value (BoolE v) v
step (PrimUnaryOp PrimFst e) = case step e of
  StepAST e' -> StepAST (PrimUnaryOp PrimFst e')
  StepValue (Value (Pair e' _) _) -> StepAST e'
  _ -> error "impossible match"
step (PrimUnaryOp PrimSnd e) = case step e of
  StepAST e' -> StepAST (PrimUnaryOp PrimSnd e')
  StepValue (Value (Pair _ e') _) -> StepAST e'
  _ -> error "impossible match"
step (PrimBinaryOp PrimAdd e1 e2) = case step e1 of
  StepAST e1' -> StepAST (PrimBinaryOp PrimAdd e1' e2)
  StepValue e1' -> case step e2 of
    StepAST e2' -> StepAST (PrimBinaryOp PrimAdd (expr e1') e2')
    StepValue e2' -> let v = (val e1') + (val e2') in StepValue $ Value (IntE v) v
step (PrimBinaryOp PrimSub e1 e2) = case step e1 of
  StepAST e1' -> StepAST (PrimBinaryOp PrimSub e1' e2)
  StepValue e1' -> case step e2 of
    StepAST e2' -> StepAST (PrimBinaryOp PrimSub (expr e1') e2')
    StepValue e2' -> let v = (val e1') - (val e2') in StepValue $ Value (IntE v) v
step (PrimBinaryOp PrimMul e1 e2) = case step e1 of
  StepAST e1' -> StepAST (PrimBinaryOp PrimMul e1' e2)
  StepValue e1' -> case step e2 of
    StepAST e2' -> StepAST (PrimBinaryOp PrimMul (expr e1') e2')
    StepValue e2' -> let v = (val e1') * (val e2') in StepValue $ Value (IntE v) v
step (PrimBinaryOp PrimDiv e1 e2) = case step e1 of
  StepAST e1' -> StepAST (PrimBinaryOp PrimDiv e1' e2)
  StepValue e1' -> case step e2 of
    StepAST e2' -> StepAST (PrimBinaryOp PrimDiv (expr e1') e2')
    StepValue e2' -> let v = (val e1') `div` (val e2') in StepValue $ Value (IntE v) v
step (PrimBinaryOp PrimAnd e1 e2) = case step e1 of
  StepAST e1' -> StepAST (PrimBinaryOp PrimAnd e1' e2)
  StepValue e1' -> case step e2 of
    StepAST e2' -> StepAST (PrimBinaryOp PrimAnd (expr e1') e2')
    StepValue e2' -> let v = (val e1') && (val e2') in StepValue $ Value (BoolE v) v
step (PrimBinaryOp PrimOr e1 e2) = case step e1 of
  StepAST e1' -> StepAST (PrimBinaryOp PrimOr e1' e2)
  StepValue e1' -> case step e2 of
    StepAST e2' -> StepAST (PrimBinaryOp PrimOr (expr e1') e2')
    StepValue e2' -> let v = (val e1') || (val e2') in StepValue $ Value (BoolE v) v
step (PrimBinaryOp PrimLT e1 e2) = case step e1 of
  StepAST e1' -> StepAST (PrimBinaryOp PrimLT e1' e2)
  StepValue e1' -> case step e2 of
    StepAST e2' -> StepAST (PrimBinaryOp PrimLT (expr e1') e2')
    StepValue e2' -> let v = (val e1') < (val e2') in StepValue $ Value (BoolE v) v
step (PrimBinaryOp PrimGT e1 e2) = case step e1 of
  StepAST e1' -> StepAST (PrimBinaryOp PrimGT e1' e2)
  StepValue e1' -> case step e2 of
    StepAST e2' -> StepAST (PrimBinaryOp PrimGT (expr e1') e2')
    StepValue e2' -> let v = (val e1') > (val e2') in StepValue $ Value (BoolE v) v
step (PrimBinaryOp PrimLE e1 e2) = case step e1 of
  StepAST e1' -> StepAST (PrimBinaryOp PrimLE e1' e2)
  StepValue e1' -> case step e2 of
    StepAST e2' -> StepAST (PrimBinaryOp PrimLE (expr e1') e2')
    StepValue e2' -> let v = (val e1') <= (val e2') in StepValue $ Value (BoolE v) v
step (PrimBinaryOp PrimGE e1 e2) = case step e1 of
  StepAST e1' -> StepAST (PrimBinaryOp PrimGE e1' e2)
  StepValue e1' -> case step e2 of
    StepAST e2' -> StepAST (PrimBinaryOp PrimGE (expr e1') e2')
    StepValue e2' -> let v = (val e1') >= (val e2') in StepValue $ Value (BoolE v) v
step (PrimBinaryOp PrimEq e1 e2) = case step e1 of
  StepAST e1' -> StepAST (PrimBinaryOp PrimEq e1' e2)
  StepValue e1' -> case step e2 of
    StepAST e2' -> StepAST (PrimBinaryOp PrimEq (expr e1') e2')
    StepValue e2' -> case (expr e1', expr e2') of
      (IntE n, IntE m) -> let v = n == m in StepValue $ Value (BoolE v) v
      (BoolE n, BoolE m) -> let v = n == m in StepValue $ Value (BoolE v) v
      (UnitE, UnitE) -> StepValue $ Value (BoolE True) True
      -- If we explicitly pattern match on conflicting cases, Haskell recognizes the conflicting constraint
      -- but we have not found yet, a way to generate an absurd value.
      _ -> error "impossible match"
step (PrimBinaryOp PrimNeq e1 e2) = case step e1 of
  StepAST e1' -> StepAST (PrimBinaryOp PrimNeq e1' e2)
  StepValue e1' -> case step e2 of
    StepAST e2' -> StepAST (PrimBinaryOp PrimNeq (expr e1') e2')
    StepValue e2' -> case (expr e1', expr e2') of
      (IntE n, IntE m) -> let v = n /= m in StepValue $ Value (BoolE v) v
      (BoolE n, BoolE m) -> let v = n /= m in StepValue $ Value (BoolE v) v
      (UnitE, UnitE) -> StepValue $ Value (BoolE False) False
      -- If we explicitly pattern match on conflicting cases, Haskell recognizes the conflicting constraint
      -- but we have not found yet, a way to generate an absurd value.
      _ -> error "impossible match"
