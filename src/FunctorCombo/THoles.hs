{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  FunctorCombo.THoles
-- Copyright   :  (c) David Feuer 2018
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Filling and extracting derivatives (one-hole contexts)
-- in 'Traversable' containers.
----------------------------------------------------------------------

module FunctorCombo.THoles (holesIn) where

import Data.Biapplicative (Bifunctor (..), Biapplicative (..), traverseBia)
import Data.Traversable (Traversable (..))

-- A lazy continuation Biapplicative, based on an idea by
-- Roman Cheplyaka.
newtype Holes t m x = Holes { runHoles :: (x -> t) -> (m, x) }

instance Bifunctor (Holes t) where
  bimap f g xs = Holes $ \xt ->
    let
      (qf, qv) = runHoles xs (xt . g)
    in (f qf, g qv)

instance Biapplicative (Holes t) where
  bipure x y = Holes $ \_ -> (x, y)
  fs <<*>> xs = Holes $ \xt ->
    let
      (pf, pv) = runHoles fs (\cd -> xt (cd qv))
      (qf, qv) = runHoles xs (\c -> xt (pv c))
    in (pf qf, pv qv)

-- | The simplest possible representation of a functor derivative
-- is a function:
--
-- @type Der f a = a -> f a@
--
-- It is possible to extract such derivatives for any
-- 'Traversable' functor; filling is then trivial.
holesIn :: Traversable t => t a -> t (a -> t a, a)
holesIn xs = fst (runHoles (traverseBia holesOne xs) id)
  where
    holesOne :: a -> Holes (t a) (a -> t a, a) a
    holesOne x = Holes $ \xt -> ((xt, x), x)
