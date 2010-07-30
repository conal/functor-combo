{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  FunctorCombo.ZipperReg
-- Copyright   :  (c) Conal Elliott 2010
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- 
----------------------------------------------------------------------

module FunctorCombo.ZipperReg
  (
    Context,Zipper, up, up', down
  ) where


import Control.Arrow (first)

-- import FunctorCombo.Derivative
-- import FunctorCombo.Holey

import FunctorCombo.DHoley
import FunctorCombo.Regular

-- TODO: Bring in pattern functors (as in PolyP), so I don't have to
-- work on fixpoints directly.  Something like
-- 
--   type Context t = [Der (PF t) t]
-- 
--   type Zipper t = (Context t, t)
-- 
-- Then use with some standard recursive data types like lists & trees.

-- TODO: Consider the implications of my style of zipper, using f (Der
-- ...), contrasted with the traditional one.  Try an application of mine
-- to make sure it's useful.  And that I avoid staring into the void.

-- TODO: rename wrap/unwrap, e.g., to reg/unreg

-- | Context for a regular type
type Context t = [Der (PF t) t]

-- | Zipper for a regular type.  Also called \"location\"
type Zipper t = (Context t, t)

-- | Move upward.  Error if empty context.
up :: (Regular t, Holey (PF t)) => Zipper t -> Zipper t
up ([]   , _) = error "up: given empty context"
up (d:ds', t) = (ds', wrap (fill (d,t)))

-- | Variant of 'up'.  'Nothing' if empty context.
up' :: (Regular t, Holey (PF t)) => Zipper t -> Maybe (Zipper t)
up' ([]   , _) = Nothing
up' l          = Just (up l)

down :: (Regular t, Holey (PF t)) => Zipper t -> PF t (Zipper t)
down (ds', t) = (fmap.first) (:ds') (extract (unwrap t))

{-

type P = Id :*: Id                      -- pairs
type Q = P  :*: P                       -- quadruples (or P :. P)

type Two  a = (a,a)

type Four a = Two (Two a)

data QuadTree a = QuadTree a (Four (QuadTree a))

instance Regular (QuadTree a) where
  type PF (QuadTree a) = Const a :*: Q
  unwrap (QuadTree a ((p,q),(r,s))) =
    Const a :*: ((Id p :*: Id q) :*: (Id r :*: Id s))
  wrap (Const a :*: ((Id p :*: Id q) :*: (Id r :*: Id s))) =
    QuadTree a ((p,q),(r,s))

-}
