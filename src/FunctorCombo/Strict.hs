{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  FunctorCombo.Strict
-- Copyright   :  (c) Conal Elliott 2010
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Strict products and sums.Strict
----------------------------------------------------------------------

module FunctorCombo.Strict
  ( (:*!)(..),curry',uncurry', (:+!)(..),either'
  ) where

infixl 7 :*!
infixl 6 :+!

{--------------------------------------------------------------------
    Products
--------------------------------------------------------------------}

-- | Strict pair
data a :*! b = !a :*! !b

-- | Curry on strict pairs
curry' :: (a :*! b -> c) -> (a -> b -> c)
curry' f a b = f (a :*! b)

-- | Uncurry on strict pairs
uncurry' :: (a -> b -> c) -> ((a :*! b) -> c)
uncurry' f (a :*! b) = f a b


{--------------------------------------------------------------------
    Sums
--------------------------------------------------------------------}

-- | Strict sum
data a :+! b = Left' !a | Right' !b

-- | Case analysis for strict sums.  Like 'either'.
either' :: (a -> c) -> (b -> c) -> (a :+! b -> c)
either' f _ (Left'  a) = f a
either' _ g (Right' b) = g b
