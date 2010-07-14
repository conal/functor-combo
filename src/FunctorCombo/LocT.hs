{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  FunctorCombo.LocT
-- Copyright   :  (c) Conal Elliott 2010
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- 
----------------------------------------------------------------------

module FunctorCombo.LocT
  (
    Context,LocT, upR, downR
  ) where


import FunctorCombo.Derivative
import FunctorCombo.Holey
import FunctorCombo.Regular

-- TODO: Bring in pattern functors (as in PolyP), so I don't have to
-- work on fixpoints directly.  Something like
-- 
--   type Context t = [Der (FunctorOf t) t]
-- 
--   type LocT t = (Context t, t)
-- 
-- Then use with some standard recursive data types like lists & trees.

-- TODO: Consider the implications of my style of zipper, using f (Der
-- ...), contrasted with the traditional one.  Try an application of mine
-- to make sure it's useful.  And that I avoid staring into the void.

-- TODO: rename wrap/unwrap, e.g., to reg/unreg

type Context t = [Der (FunctorOf t) t]

type LocT t = (Context t, t)

upR :: (Regular t, Holey (FunctorOf t)) => LocT t -> LocT t
upR ([],_) = error "up: already at top"
upR (d:ds', t) = (ds', wrap (fill (d,t)))


downR :: (Regular t, Holey (FunctorOf t)) => LocT t -> FunctorOf t (LocT t)
downR (ds', t) = fmap (\ (d,t') -> (d:ds',t')) (extract (unwrap t))

{-

type P = Id :*: Id                      -- pairs
type Q = P  :*: P                       -- quadruples (or P :. P)

type Two  a = (a,a)

type Four a = Two (Two a)

data QuadTree a = QuadTree a (Four (QuadTree a))

instance Regular (QuadTree a) where
  type FunctorOf (QuadTree a) = Const a :*: Q
  unwrap (QuadTree a ((p,q),(r,s))) =
    Const a :*: ((Id p :*: Id q) :*: (Id r :*: Id s))
  wrap (Const a :*: ((Id p :*: Id q) :*: (Id r :*: Id s))) =
    QuadTree a ((p,q),(r,s))

-}
