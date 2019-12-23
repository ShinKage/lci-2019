{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}

-------------------------------------------------------------------------------
-- |
-- Module      : Data.List.Extra
-- Description : Additional (dependent) predicates on regular lists.
-- Copyright   : (c) Giuseppe Lomurno, 2019
-- License     : ...
-- Maintainer  : Giuseppe Lomurno <g.lomurno@studenti.unipi.it>
-- Stability   : experimental
-- Portability : non-portable (?)
--
-------------------------------------------------------------------------------

module Data.List.Extra where

import Data.Kind
import Data.Singletons.Prelude hiding (Elem)
import Data.Singletons.Sigma

-- | Proof that the index element is in the index list.
data Elem :: [a] -> a -> Type where
  Here  :: Elem (x : xs) x
  There :: Elem xs x -> Elem (y : xs) x

deriving instance Show (Elem xs x)

-- | Returns the element at the index represented by the 'Elem' proof.
index :: Elem xs x -> SList xs -> Sing x
index Here      (SCons x _)  = x
index (There e) (SCons _ xs) = index e xs

-- | Recovers the position inside the list from the proof.
elemToIntegral :: Integral n => Elem xs x -> n
elemToIntegral Here      = 0
elemToIntegral (There e) = 1 + elemToIntegral e

-- | Given a list, in singleton form required for dependent constructs,
-- checks whether the provided index is a valid index and builds a proof
-- for the element pointend by the index.
maybeElem :: SList (xs :: [a]) -> Int -> Maybe (Sigma a (TyCon (Elem xs)))
maybeElem SNil _ = Nothing
maybeElem (SCons x xs) idx
  | idx < 0   = Nothing
  | idx == 0  = Just (x :&: Here)
  | otherwise = maybeElem xs (idx - 1) >>= \case
                  y :&: prf -> Just $ y :&: There prf

-- | Runtime (dependent) representation of a list length.
data Length :: [a] -> Type where
  LZ :: Length '[]
  LS :: Length xs -> Length (x : xs)

deriving instance Show (Length xs)

-- | Given a proof that an element x is inside the list xs, it builds a proof
-- that x is an element of the list with another list prefixed to xs.
weakenElem :: Length prefix -> Elem xs x -> Elem (prefix ++ xs) x
weakenElem LZ       e = e
weakenElem (LS len) e = There $ weakenElem len e
