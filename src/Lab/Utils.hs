{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

-------------------------------------------------------------------------------
-- |
-- Module      : Lab.Utils
-- Description : Utility functions.
-- Copyright   : (c) Giuseppe Lomurno, 2019
-- License     : ...
-- Maintainer  : Giuseppe Lomurno <g.lomurno@studenti.unipi.it>
-- Stability   : experimental
-- Portability : non-portable (?)
--
-------------------------------------------------------------------------------

module Lab.Utils where

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal

import Lab.Types

type Prec = Rational

initPrec, lambdaPrec, appPrec, appLeftPrec, appRightPrec, ifPrec :: Prec
initPrec     = 0
lambdaPrec   = 1
appPrec      = 9
appLeftPrec  = 9
appRightPrec = 9
ifPrec       = 1

binOpPrecs :: BinaryOp arg1 arg2 res -> (Prec, Prec, Prec)
binOpPrecs PrimAdd = (5, 4.9, 5)
binOpPrecs PrimSub = (5, 4.9, 5)
binOpPrecs PrimMul = (6, 5.9, 6)
binOpPrecs PrimDiv = (6, 5.9, 6)
binOpPrecs PrimLT  = (4, 4, 4)
binOpPrecs PrimGT  = (4, 4, 4)
binOpPrecs PrimLE  = (4, 4, 4)
binOpPrecs PrimGE  = (4, 4, 4)
binOpPrecs PrimEq  = (4, 4, 4)
binOpPrecs PrimNeq = (4, 4, 4)
binOpPrecs PrimAnd = (3, 3, 3)
binOpPrecs PrimOr  = (2, 2, 2)

unOpPrec :: UnaryOp arg res -> (Prec, Prec)
unOpPrec PrimNeg = (6, 6)
unOpPrec PrimNot = (6, 6)
unOpPrec PrimFst = (6, 6)
unOpPrec PrimSnd = (6, 6)

opPrec, opPrecArg :: UnaryOp arg res -> Prec
opPrec    (unOpPrec -> (x, _)) = x
opPrecArg (unOpPrec -> (_, x)) = x

binOpPrec, binOpLeftPrec, binOpRightPrec :: BinaryOp arg1 arg2 res -> Prec
binOpPrec      (binOpPrecs -> (x, _, _)) = x
binOpLeftPrec  (binOpPrecs -> (_, x, _)) = x
binOpRightPrec (binOpPrecs -> (_, _, x)) = x

-- | Enclose a 'Doc' in parens if the flag is 'True'
maybeParens :: Bool -> Doc ann -> Doc ann
maybeParens True  = parens
maybeParens False = id

colorVar :: Int -> Doc AnsiStyle -> Doc AnsiStyle
colorVar i = annotate (color $ colors !! i)
  where colors :: [Color]
        colors = cycle [Red, Green, Yellow, Blue, Magenta, Cyan]

allPairs :: [a] -> [(a, a)]
allPairs []  = []
allPairs [_] = []
allPairs (x : xs) = map (x,) xs ++ allPairs xs
