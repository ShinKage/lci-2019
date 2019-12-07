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

module Lab.Eval (Value(..), eval) where

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
