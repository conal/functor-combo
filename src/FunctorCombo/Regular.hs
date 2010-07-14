{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  FunctorCombo.Regular
-- Copyright   :  (c) Conal Elliott 2010
-- License     :  GPL-3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Regular data types
----------------------------------------------------------------------

module FunctorCombo.Regular
  (
    Regular(..)
  ) where

import Control.Applicative ((<$>))

import Data.Tree

import FunctorCombo.Functor


-- Pattern functors, similar to PolyC and the Regular class from
-- UU (e.g., "A Lightweight Approach to Datatype-Generic Rewriting")

class Functor (FunctorOf t) => Regular t where
  type FunctorOf t :: * -> *
  wrap   :: FunctorOf t t -> t
  unwrap :: t -> FunctorOf t t


-- Some Regular instances:

instance Regular [a] where
  type FunctorOf [a] = Unit :+: Const a :*: Id
  unwrap []     = L (Const ())
  unwrap (a:as) = R (Const a :*: Id as)
  wrap (L (Const ()))          = []
  wrap (R (Const a :*: Id as)) = a:as


-- Rose tree (from Data.Tree)
-- 
--   data Tree  a = Node a [Tree a]

instance Regular (Tree a) where
  type FunctorOf (Tree a) = Const a :*: ([] :. Id)
  unwrap (Node a ts) = Const a :*: O (Id <$> ts)
  wrap (Const a :*: O (idTs)) = Node a (unId <$> idTs)


-- instance Functor Tree where
--   fmap f (Node a ts) = Node (f a) ((fmap.fmap) f ts)

-- Try defining more generally:
-- 
-- instance Functor Tree where
--   fmap f = wrap . (fmap.fmap) f . unwrap

{-
f :: a -> b

t :: Tree a

unwrap t :: FunctorOf (Tree a) (Tree a)

(fmap.fmap) f (unwrap t) :: FunctorOf (Tree a) (Tree b)

wrap ((fmap.fmap) f (unwrap t)) :: oops

I need a variation on fmap.  Maybe

   fmap' :: (a -> b) -> FunctorOf (h a) (h a) -> FunctorOf (h b) (h b)

I think PolyP dealt with this issue via something like Bifunctor and
used Par and Rec.

-}
