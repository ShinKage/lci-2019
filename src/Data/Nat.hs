{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}

-------------------------------------------------------------------------------
-- |
-- Module      : Data.Nat
-- Description : Peano natural numbers.
-- Copyright   : (c) Giuseppe Lomurno, 2019
-- License     : ...
-- Maintainer  : Giuseppe Lomurno <g.lomurno@studenti.unipi.it>
-- Stability   : experimental
-- Portability : non-portable (?)
--
-------------------------------------------------------------------------------

module Data.Nat where

import Data.Singletons.Prelude
import Data.Singletons.TH

$(singletons [d|
  -- | Inductive definition of Peano natural numbers.
  data Nat = Z | S Nat deriving (Eq, Show, Ord)

  instance Num Nat where
    n   - Z   = n
    S n - S m = n - m

    Z     + n = n
    (S m) + n = S (m + n)

    Z     * _ = 0
    (S m) * n = m * n + n

    abs = id

    signum Z     = Z
    signum (S _) = S Z

    -- No singletons pattern matching available for literals
    fromInteger n = if n <= 0 then Z else S (fromInteger (n - 1))
  |])
