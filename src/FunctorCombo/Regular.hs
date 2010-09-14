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

-- import Data.Tree

-- import FunctorCombo.Functor


-- Pattern functors, similar to PolyC and the Regular class from
-- UU (e.g., "A Lightweight Approach to Datatype-Generic Rewriting")

class Functor (PF t) => Regular t where
  type PF t :: * -> *
  wrap   :: PF t t -> t
  unwrap :: t -> PF t t

{-

-- For now, move these instances to StrictMemo and NonstrictMemo, since I
-- want different instances, depending on how careful I'm taking care with
-- bottoms.

-- Some Regular instances:

-- instance Regular [a] where
--   type PF [a] = Unit :+: Const a :*: Id
--   unwrap []     = InL (Const ())
--   unwrap (a:as) = InR (Const a :*: Id as)
--   wrap (InL (Const ()))          = []
--   wrap (InR (Const a :*: Id as)) = a:as


instance Regular [a] where
  type PF [a] = Unit :+:! Const (Lift a) :*:! Lift
  unwrap []     = InL' (Const ())
  unwrap (a:as) = InR' (Const (Lift a) :*:! Lift as)
  wrap (InL' (Const ()))            = []
  wrap (InR' (Const (Lift a) :*:! Lift as)) = a:as


-- Rose tree (from Data.Tree)
-- 
--   data Tree  a = Node a [Tree a]

-- instance Functor Tree where
--   fmap f (Node a ts) = Node (f a) (fmap f ts)

instance Regular (Tree a) where
  type PF (Tree a) = Const a :*: []
  unwrap (Node a ts) = Const a :*: ts
  wrap (Const a :*: ts) = Node a ts

-- Note that we're using the non-strict pairing functor.
-- Does PF (Tree a) have the right strictness?
-- I think so, since a tree can be either _|_ or Node applied to a
-- possibly-_|_ value and a possibly-_|_ list.

-}
