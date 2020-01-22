{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

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

module Lab.Decls where

import           Control.Monad.Reader
import           Control.Monad.State
import qualified Control.Monad.State.Strict as Strict
import           Control.Monad.Writer.Strict
import           Data.Bifunctor
import           Data.Hashable
import           Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HMap
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HSet
import           Data.Kind
import           Data.List.Extra
import           Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import           Data.Maybe (fromMaybe)
import           Data.Singletons.Prelude (Sing(..), fromSing)
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.Terminal
import           Data.Text.Prettyprint.Doc.Symbols.Unicode

import           Lab.AST
import           Lab.Types
import           Lab.Utils

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
  -- | Recursion call token, must be present only in top-level declarations.
  CRecToken :: CodegenAST
  -- | Lazy expression computation for CSE.
  CLet :: CodegenAST -> CodegenAST -> CodegenAST
  -- | Reference to a lazy expression computation.
  CLetRef :: Int -> CodegenAST

deriving instance Show CodegenAST

-- | A top-level function declaration.
data Declaration = Decl { argsType :: [LType]
                        , retType  :: LType
                        , body     :: CodegenAST
                        }
  deriving (Show)

-- | An environment for code generation with a list of declarations
-- and the expression to execute.
data CodegenEnv = Env { decl :: Map Int Declaration
                      , expr :: CodegenAST
                      }
  deriving (Show)

instance Eq CodegenAST where
  (CIntE n) == (CIntE m) = n == m
  (CBoolE b) == (CBoolE v) = b == v
  CUnitE == CUnitE = True
  (CPrimUnaryOp op e) == (CPrimUnaryOp op' e') = op `eqUnary` op' && e == e'
  (CPrimBinaryOp op e1 e2) == (CPrimBinaryOp op' e1' e2') = op `eqBinary` op' && e1 == e1' && e2 == e2'
  (CCond c e1 e2) == (CCond c' e1' e2') = c == c' && e1 == e1' && e2 == e2'
  (CVar n) == (CVar n') = n == n'
  (CPair e1 e2) == (CPair e1' e2') = e1 == e1' && e2 == e2'
  (CCall n) == (CCall n') = n == n'
  (CLambda arg ret e) == (CLambda arg' ret' e') = arg == arg' && ret == ret' && e == e'
  (CApp lam arg) == (CApp lam' arg') = lam == lam' && arg == arg'
  (CFix e) == (CFix e') = e == e'
  CRecToken == CRecToken = True
  (CLetRef n) == (CLetRef n') = n == n'
  _ == _ = False

instance Hashable CodegenAST where
  hashWithSalt s (CIntE n)  = s `hashWithSalt` n
  hashWithSalt s (CBoolE b) = s `hashWithSalt` b
  hashWithSalt s CUnitE     = s `hashWithSalt` ()
  hashWithSalt s (CPrimUnaryOp op e) = s `hashWithSalt` op
                                         `hashWithSalt` e
  hashWithSalt s (CPrimBinaryOp op e1 e2) = s `hashWithSalt` op
                                              `hashWithSalt` e1
                                              `hashWithSalt` e2
  hashWithSalt s (CCond c e1 e2) = s `hashWithSalt` c
                                     `hashWithSalt` e1
                                     `hashWithSalt` e2
  hashWithSalt s (CVar n) = s `hashWithSalt` n
  hashWithSalt s (CPair e1 e2) = s `hashWithSalt` e1
                                   `hashWithSalt` e2
  hashWithSalt s (CCall n) = s `hashWithSalt` n
  hashWithSalt s (CLambda arg ret e) = s `hashWithSalt` arg
                                         `hashWithSalt` ret
                                         `hashWithSalt` e
  hashWithSalt s (CApp lam arg) = s `hashWithSalt` lam
                                    `hashWithSalt` arg
  hashWithSalt s (CFix e) = s `hashWithSalt` e
  hashWithSalt s CRecToken = s `hashWithSalt` "rec"
  hashWithSalt s (CLet lam arg) = s `hashWithSalt` lam
                                    `hashWithSalt` arg
  hashWithSalt s (CLetRef n) = s `hashWithSalt` n

-- | Pretty printing a code generation ready AST.
prettyCodegenAST :: CodegenAST -> Doc AnsiStyle
prettyCodegenAST = flip Strict.evalState ((0, 0), initPrec) . go
  where updatePrec :: Prec -> ((Int, Int), Prec) -> ((Int, Int), Prec)
        updatePrec p (i, _) = (i, p)

        updateLamCount :: Int -> ((Int, Int), Prec) -> ((Int, Int), Prec)
        updateLamCount l ((_, b), c) = ((l, b), c)

        updateLetCount :: Int -> ((Int, Int), Prec) -> ((Int, Int), Prec)
        updateLetCount l ((b, _), c) = ((b, l), c)

        go :: CodegenAST -> Strict.State ((Int, Int), Prec) (Doc AnsiStyle)
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
        go (CVar v) = pure $ pretty '#' <> pretty v
        go (CCall v) = pure $ pretty "call" <+> pretty v
        go (CLambda args _ e) = do
          prec <- gets snd
          old <- gets (fst . fst)
          e' <- Strict.withState (updatePrec initPrec) $ go e
          modify $ updateLamCount (old + 1)
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
        go (CLet e1 e2) = do
          prec <- gets snd
          old <- gets (snd . fst)
          e1' <- Strict.withState (updatePrec initPrec) $ go e1
          e2' <- Strict.withState (updatePrec initPrec) $ go e2
          modify $ updateLetCount (old + 1)
          pure $ maybeParens (prec >= lambdaPrec) $
            fillSep [ pretty "let" <+> pretty "#l" <> pretty old <+> pretty "=" <+> e1'
                    , pretty "in" <+> e2'
                    ]
        go (CLetRef v) = pure $ pretty "#l" <> pretty v

-- | Conversion from a typed AST to a code generation ready IR.
fromAST :: Sing env -> AST env ty -> CodegenAST
fromAST = fromAST' 0

fromAST' :: Int -> Sing env -> AST env ty -> CodegenAST
fromAST' _ _ (IntE n)  = CIntE n
fromAST' _ _ (BoolE b) = CBoolE b
fromAST' _ _ UnitE     = CUnitE
fromAST' _ _ (Var (elemToIntegral -> v)) = CVar v
fromAST' vars env (PrimUnaryOp op e) = CPrimUnaryOp op (fromAST' vars env e)
fromAST' vars env (PrimBinaryOp op e1 e2) = CPrimBinaryOp op (fromAST' vars env e1) (fromAST' vars env e2)
fromAST' vars env (Cond c e1 e2) = CCond (fromAST' vars env c) (fromAST' vars env e1) (fromAST' vars env e2)
fromAST' vars env (Pair e1 e2) = CPair (fromAST' vars env e1) (fromAST' vars env e2)
fromAST' vars env (Lambda sty e) = let env' = SCons sty env in
                                       CLambda [fromSing sty] (fromSing $ returnType env' e) (fromAST' vars env' e)
fromAST' vars env (App lam arg) = CApp (fromAST' vars env lam) (fromAST' vars env arg)
fromAST' vars env (Fix e) = CFix (fromAST' vars env e)

-- | Returns the list of free variable used in the expression.
freeVars :: CodegenAST -> [(LType, Int)]
freeVars = freeVars' 0 []

freeVars' :: Int -> [LType] -> CodegenAST -> [(LType, Int)]
freeVars' i types (CPrimBinaryOp _ e1 e2) = freeVars' i types e1 ++ freeVars' i types e2
freeVars' i types (CPrimUnaryOp _ e) = freeVars' i types e
freeVars' i types (CCond c e1 e2) = freeVars' i types c ++ freeVars' i types e1 ++ freeVars' i types e2
freeVars' i types (CVar v) = [(types !! v, v - i) | v >= i] -- types is the list of abstraction arguments discovered during descent.
                                                            -- a variable is free if it is outside the range of types that is passed as the arg i.
freeVars' i types (CPair e1 e2) = freeVars' i types e1 ++ freeVars' i types e2
freeVars' i types (CApp lam arg) = freeVars' i types lam ++ freeVars' i types arg
freeVars' i types (CLambda argsTy _ e) = freeVars' (i + length argsTy) (argsTy ++ types) e
freeVars' i types (CFix e) = freeVars' i types e
freeVars' i types (CLet e1 e2) = freeVars' i types e1 ++ freeVars' i types e2
freeVars' _ _ _ = []

-- | Applies the closure conversion transformation to the expression.
closureConv :: CodegenAST -> CodegenAST
closureConv = flip runReader [] . closureConv'

closureConv' :: CodegenAST -> Reader [LType] CodegenAST
closureConv' lam@(CLambda vs ret e) = do
  e' <- local (vs ++) (closureConv' e)
  types <- ask
  let vars = freeVars' 0 types lam
  pure $ CLambda (fmap fst vars ++ vs) ret e' `applyTo` map snd vars
closureConv' (CPrimUnaryOp op e) = CPrimUnaryOp op <$> closureConv' e
closureConv' (CPrimBinaryOp op e1 e2) = CPrimBinaryOp op <$> closureConv' e1 <*> closureConv' e2
closureConv' (CCond c e1 e2) = CCond <$> closureConv' c <*> closureConv' e1 <*> closureConv' e2
closureConv' (CPair e1 e2) = CPair <$> closureConv' e1 <*> closureConv' e2
closureConv' (CApp lam arg) = CApp <$> closureConv' lam <*> closureConv' arg
closureConv' (CFix e) = CFix <$> closureConv' e
closureConv' (CLet e1 e2) = CLet <$> closureConv' e1 <*> closureConv' e2
closureConv' e = pure e

applyTo :: CodegenAST -> [Int] -> CodegenAST
applyTo = foldl (\e a -> CApp e $ CVar a)

-- | Applies the lambda lifting transformation to the expression.
liftLam :: CodegenAST -> WriterT (Map Int Declaration) (State Int) CodegenAST
liftLam (CLambda vs ret e) = do
  fresh <- get
  put $ fresh + 1
  e' <- liftLam e
  tell $ Map.singleton fresh $ Decl vs ret e'
  pure $ CCall fresh
liftLam (CPrimUnaryOp op e) = CPrimUnaryOp op <$> liftLam e
liftLam (CPrimBinaryOp op e1 e2) = CPrimBinaryOp op <$> liftLam e1 <*> liftLam e2
liftLam (CCond c e1 e2) = CCond <$> liftLam c <*> liftLam e1 <*> liftLam e2
liftLam (CPair e1 e2) = CPair <$> liftLam e1 <*> liftLam e2
liftLam (CApp lam arg) = CApp <$> liftLam lam <*> liftLam arg
liftLam (CFix lam) = liftLam lam
liftLam (CLet e1 e2) = CLet <$> liftLam e1 <*> liftLam e2
liftLam e = pure e

-- | Joins sequences of lambda abstractions in a single multi-parameter lambda
-- abstraction.
smash :: CodegenAST -> CodegenAST
smash (CLambda vs _ (CLambda vs' ret' e)) = smash (CLambda (vs ++ vs') ret' e)
smash (CLambda vs ret e) = CLambda vs ret (smash e)
smash (CPrimBinaryOp op e1 e2) = CPrimBinaryOp op (smash e1) (smash e2)
smash (CPrimUnaryOp op e) = CPrimUnaryOp op (smash e)
smash (CCond c e1 e2) = CCond (smash c) (smash e1) (smash e2)
smash (CPair e1 e2) = CPair (smash e1) (smash e2)
smash (CApp lam arg) = CApp (smash lam) (smash arg)
smash (CFix (CLambda vs ret e)) = CFix (CLambda vs ret (smash e))
smash (CLet e1 e2) = CLet (smash e1) (smash e2)
smash (CFix e) = CFix (smash e)
smash e = e

-- | Removes explicit fix operator with recursive call tokens ready for codegen.
-- Assumes that the next expression in the tree after the fixpoint operator is
-- a lambda abstraction (currently this is enforced by the type checker).
unfix :: CodegenAST -> CodegenAST
unfix = flip runReader (False, 0) . unfix'

unfix' :: CodegenAST -> Reader (Bool, Int) CodegenAST
unfix' (CPrimUnaryOp op e) = CPrimUnaryOp op <$> unfix' e
unfix' (CPrimBinaryOp op e1 e2) = CPrimBinaryOp op <$> unfix' e1 <*> unfix' e2
unfix' (CCond c e1 e2) = CCond <$> unfix' c <*> unfix' e1 <*> unfix' e2
unfix' (CPair e1 e2) = CPair <$> unfix' e1 <*> unfix' e2
unfix' (CApp lam arg) = CApp <$> unfix' lam <*> unfix' arg
unfix' (CLet e1 e2) = CLet <$> unfix' e1 <*> local (second (+ 1)) (unfix' e2)
unfix' (CVar e) = do
  (seen, vars) <- ask
  pure $ if seen && vars == e then CRecToken else CVar e
unfix' (CLambda sty ret e) = do
  (seen, vars) <- ask
  e' <- local (const (seen, if seen then vars + length sty else vars)) (unfix' e)
  pure $ CLambda sty ret e'
unfix' (CFix (CLambda _ _ e)) = do
  (seen, vars) <- ask
  if seen then error "Unsupported nested fixes"
          else local (const (True, vars)) (unfix' e)
unfix' (CFix _) = error "Unsupported lambda reference in fix operator"
unfix' e = pure e

-- | Builds a code generation ready environment from a combinator with the final expression
-- and a list of lifted lambda abstractions, all with performed CSE.
buildEnv :: AST '[] ty -> CodegenEnv
buildEnv ast = let (code, ds) = flip evalState 0 . runWriterT . liftLam . closureConv . unfix . smash $ fromAST SNil ast
                   ds' = fmap (\d -> d { body = cse (body d) }) ds in
                   Env ds' (cse code)

-- | Performes Common Subexpression Elimination.
cse :: CodegenAST -> CodegenAST
cse = zapLets . replaceLets . insertLets

-- | Descend in the AST accumulating a set of subexpression, when ascending
-- if a subexpression was already seen, inserts a lazy let.
insertLets :: CodegenAST -> CodegenAST
insertLets = fst . go
  where go :: CodegenAST -> (CodegenAST, HashSet CodegenAST)
        go e@(CIntE _) = (e, HSet.empty)
        go e@(CBoolE _) = (e, HSet.empty)
        go e@CUnitE = (e, HSet.empty)
        go (CPrimUnaryOp op e) = let (e', set) = go e in
                                     update (CPrimUnaryOp op e') [set]
        go (CPrimBinaryOp op e1 e2) = let (e1', set1) = go e1
                                          (e2', set2) = go e2 in
                                          update (CPrimBinaryOp op e1' e2') [set1, set2]
        go (CCond c e1 e2) = let (c', set1) = go c
                                 (e1', set2) = go e1
                                 (e2', set3) = go e2 in
                                 update (CCond c' e1' e2') [set1, set2, set3]
        go e@(CVar _) = (e, HSet.empty)
        go (CPair e1 e2) = let (e1', set1) = go e1
                               (e2', set2) = go e2 in
                               update (CPair e1' e2') [set1, set2]
        go e@(CCall _) = (e, HSet.empty)
        go (CLambda arg ret e) = let (e', set) = go e in
                                     update (CLambda arg ret e') [set]
        go (CApp lam arg) = let (lam', set1) = go lam
                                (arg', set2) = go arg in
                                update (CApp lam' arg') [set1, set2]
        go (CFix e) = let (e', set) = go e in update (CFix e') [set]
        go e@CRecToken = (e, HSet.empty)
        go (CLet _ _) = error "why lets so early?"
        go (CLetRef _) = error "why lets so early?"

        -- | Updates a list of sets with a new subexpression and joins them.
        update :: CodegenAST -> [HashSet CodegenAST] -> (CodegenAST, HashSet CodegenAST)
        update e all_exprss = (mkLets common_exprs e, HSet.insert e all_exprs)
          where
            pairs = allPairs all_exprss
            inters = map (uncurry HSet.intersection) pairs
            common_exprs = HSet.toList (HSet.unions inters)
            all_exprs = HSet.unions all_exprss

-- | Replaces common subexpressions that have been lifted to lazy lets with a reference to
-- the their proper let.
replaceLets :: CodegenAST -> CodegenAST
replaceLets = go HMap.empty
  where go :: HashMap CodegenAST Int -> CodegenAST -> CodegenAST
        go m e | Just v <- HMap.lookup e m = CLetRef v
        go m (CLet e1 e2) = let e1' = go m e1
                                m' = addMapping (shiftRef 1 e1) $ addMapping (shiftRef 1 e1') (shiftMap m) in
                                CLet e1' (go m' e2)
        go m (CPrimUnaryOp op e) = CPrimUnaryOp op (go m e)
        go m (CPrimBinaryOp op e1 e2) = CPrimBinaryOp op (go m e1) (go m e2)
        go m (CCond c e1 e2) = CCond (go m c) (go m e1) (go m e2)
        go m (CPair e1 e2) = CPair (go m e1) (go m e2)
        go m (CLambda sty ret e) = CLambda sty ret (go m e)
        go m (CApp lam arg) = CApp (go m lam) (go m arg)
        go m (CFix e) = CFix (go m e)
        go _ e = e

        addMapping e = insertIfAbsent e 0

-- | During the insert and replace process multiple lets with the same subexpression
-- could have been added. This function leaves only the topmost level lazy let.
zapLets :: CodegenAST -> CodegenAST
zapLets = fst . go HMap.empty
  where go :: HashMap Int Int -> CodegenAST -> (CodegenAST, HashSet Int)
        go m (CLet e1 e2) | CLetRef v <- e1 = let (e2', used_vars) = go (HMap.insert 0 (v + 1) (shiftRefMap m)) e2
                                                  e2'' = shiftRef (-1) e2' in
                                                  (e2'', shiftSet (-1) used_vars)
                          | otherwise = let (e1', used_vars1) = go m e1
                                            (e2', used_vars2) = go (shiftRefMap m) e2
                                            used_vars2' = shiftSet (-1) used_vars2 in
                                            if HSet.member 0 used_vars2
                                               then (CLet e1' e2', HSet.unions [used_vars1, used_vars2'])
                                               else (shiftRef (-1) e2', used_vars2')
        go m e@(CLetRef v) | Just v' <- HMap.lookup v m = (CLetRef v', HSet.singleton v')
                           | otherwise = (e, HSet.singleton v)
        go m (CLambda sty ret e) = let (e', used_vars) = go m e in
                                       (CLambda sty ret e', used_vars)
        go m (CApp e1 e2) = let (e1', used_vars1) = go m e1
                                (e2', used_vars2) = go m e2 in
                                (CApp e1' e2', HSet.union used_vars1 used_vars2)
        go m (CPrimUnaryOp op e) = let (e', used_vars) = go m e in
                                       (CPrimUnaryOp op e', used_vars)
        go m (CPrimBinaryOp op e1 e2) = let (e1', used_vars1) = go m e1
                                            (e2', used_vars2) = go m e2 in
                                            (CPrimBinaryOp op e1' e2', HSet.union used_vars1 used_vars2)
        go m (CCond c e1 e2) = let (c', used_vars1) = go m c
                                   (e1', used_vars2) = go m e1
                                   (e2', used_vars3) = go m e2 in
                                   (CCond c' e1' e2', HSet.unions [used_vars1, used_vars2, used_vars3])
        go m (CPair e1 e2) = let (e1', used_vars1) = go m e1
                                 (e2', used_vars2) = go m e2 in
                                 (CPair e1' e2', HSet.union used_vars1 used_vars2)
        go m (CFix e) = let (e', used_vars) = go m e in
                            (CFix e', used_vars)
        go _ e = (e, HSet.empty)


mkLets :: [CodegenAST] -> CodegenAST -> CodegenAST
mkLets es b = foldr CLet b es

shiftRef :: Int -> CodegenAST -> CodegenAST
shiftRef i (CPrimUnaryOp op e) = CPrimUnaryOp op (shiftRef i e)
shiftRef i (CPrimBinaryOp op e1 e2) = CPrimBinaryOp op (shiftRef i e1) (shiftRef i e2)
shiftRef i (CCond c e1 e2) = CCond (shiftRef i c) (shiftRef i e1) (shiftRef i e2)
shiftRef i (CLetRef e) = CLetRef (e + i)
shiftRef i (CPair e1 e2) = CPair (shiftRef i e1) (shiftRef i e2)
shiftRef i (CLambda sty ret e) = CLambda sty ret (shiftRef i e)
shiftRef i (CApp lam arg) = CApp (shiftRef i lam) (shiftRef i arg)
shiftRef i (CFix e) = CFix (shiftRef i e)
shiftRef i (CLet e1 e2) = CLet (shiftRef i e1) (shiftRef i e2)
shiftRef _ e = e

shiftMap :: HashMap CodegenAST Int -> HashMap CodegenAST Int
shiftMap = HMap.foldrWithKey go HMap.empty
  where go e el = HMap.insert (shiftRef 1 e) (el + 1)

shiftRefMap :: HashMap Int Int -> HashMap Int Int
shiftRefMap = HMap.foldrWithKey go HMap.empty
  where go e el = HMap.insert (e + 1) (el + 1)

shiftSet :: Int -> HashSet Int -> HashSet Int
shiftSet i = HSet.map (+ i)

insertIfAbsent :: (Eq k, Hashable k) => k -> v -> HashMap k v -> HashMap k v
insertIfAbsent k v = HMap.alter (Just . fromMaybe v) k
