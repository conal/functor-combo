-- {-# LANGUAGE #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  FunctorCombo.ZipperFix
-- Copyright   :  (c) Conal Elliott 2010
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Zippers for functor fixpoints
----------------------------------------------------------------------

module FunctorCombo.ZipperFix (Context,Zipper, up,up',down) where

import Control.Arrow (first)

-- import FunctorCombo.Derivative
-- import FunctorCombo.Holey

import FunctorCombo.DHoley


newtype Fix f = Fix { unFix :: f (Fix f) }

-- If Haskell had recursive type synonyms:
-- 
--   Fix f =~ f (Fix f)


-- | Context for functor fixpoints

-- data Context f = Context (Der f (Fix f)) (Context f)

-- type Context f = Stream (Der f (Fix f))

-- Or, if we want topped data types:

-- data Context f = TopC | Context (Der f (Fix f)) (Context f)

-- Isomorphically:


-- | Context for a regular type
type Context f = [Der f (Fix f)]

-- Reminder:
-- 
--   type Loc f a = (Der f a, a)

-- Instead,

-- | Zipper for a functor tree.  Also called \"location\"
type Zipper f = (Context f, Fix f)

-- TODO: can I relate Context to Der (Fix f) and use Loc for Zipper?

-- | Move upward.  Error if empty context.
up :: Holey f => Zipper f -> Zipper f
up ([]   , _) = error "up: given empty context"
up (d:ds', t) = (ds', Fix (fill (d,t)))

-- | Variant of 'up'.  'Nothing' if empty context.
up' :: Holey f => Zipper f -> Maybe (Zipper f)
up' ([]   , _) = Nothing
up' l          = Just (up l)

{-

(d:ds', t) :: Zipper f
(d:ds', t) :: (Context f, Fix f)

d:ds' :: [Der f (Fix f)]

t :: Fix f

d   ::  Der f (Fix f)
ds' :: [Der f (Fix f)]

fill :: Loc f b -> f b

fill (d,t) :: f (Fix f)

Fix (fill (d,t)) :: Fix f

-}

down :: Holey f => Zipper f -> f (Zipper f)
down (ds', t) = (fmap.first) (:ds') (extract (unFix t))

-- down (ds', t) = fmap (\ (d,t') -> (d:ds',t')) (extract (unFix t))



{-
(ds',t) :: Zipper f
(ds',t) :: (Context f, Fix f)
(ds',t) :: ([Der f (Fix f)], Fix f)

ds' :: [Der f (Fix f)]
t :: Fix f
unFix t :: f (Fix f)

extract (unFix t) :: f (Der f (Fix f), Fix f)

(fmap.first) (:ds') (extract (unFix t))
  :: ([Der f (Fix f)], Fix f)
  :: (Context f, Fix f)
  :: Zipper f
-}
