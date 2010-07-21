{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  FunctorCombo.Regular
-- Copyright   :  (c) Conal Elliott 2010
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Regular data types
----------------------------------------------------------------------

module FunctorCombo.Regular (Regular(..)) where

import Data.Tree

import FunctorCombo.Functor


-- Pattern functors, similar to PolyC and the Regular class from
-- UU (e.g., "A Lightweight Approach to Datatype-Generic Rewriting")

class Functor (PF t) => Regular t where
  type PF t :: * -> *
  wrap   :: PF t t -> t
  unwrap :: t -> PF t t


-- Some Regular instances:

instance Regular [a] where
  type PF [a] = Unit :+: Const a :*: Id
  unwrap []     = InL (Const ())
  unwrap (a:as) = InR (Const a :*: Id as)
  wrap (InL (Const ()))          = []
  wrap (InR (Const a :*: Id as)) = a:as


-- Rose tree (from Data.Tree)
-- 
--   data Tree  a = Node a [Tree a]

-- instance Functor Tree where
--   fmap f (Node a ts) = Node (f a) (fmap f ts)

instance Regular (Tree a) where
  type PF (Tree a) = Const a :*: []
  unwrap (Node a ts) = Const a :*: ts
  wrap (Const a :*: ts) = Node a ts
