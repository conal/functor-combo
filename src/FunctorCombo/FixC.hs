-- {-# LANGUAGE #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  FunctorCombo.FixC
-- Copyright   :  (c) Conal Elliott 2010
-- License     :  GPL-3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Zippers for functor fixpoints
----------------------------------------------------------------------

module FunctorCombo.FixC (FixC,LocFix, up,down) where

import FunctorCombo.Derivative
import FunctorCombo.Holey



newtype Fix f = Fix (f (Fix f))

-- If Haskell had recursive type synonyms:
-- 
--   Fix f =~ f (Fix f)


-- | Context for functor fixpoints

-- data FixC f = FixC (Der f (Fix f)) (FixC f)

-- type FixC f = Stream (Der f (Fix f))

-- Or, if we want topped data types:

-- data FixC f = TopC | FixC (Der f (Fix f)) (FixC f)

-- Isomorphically:

type FixC f = [Der f (Fix f)]

-- Reminder:
-- 
--   type Loc f a = (Der f a, a)

-- Instead,

type LocFix f = (FixC f, Fix f)

-- TODO: can I relate FixC to Der (Fix f) and use Loc for LocFix?

up :: Holey f => LocFix f -> LocFix f
up ([],_) = error "up: already at top"
up (d:ds', t) = (ds', Fix (fill (d,t)))

{-

(d:ds', t) :: LocFix f
(d:ds', t) :: (FixC f, Fix f)

d:ds' :: [Der f (Fix f)]

t :: Fix f

d   ::  Der f (Fix f)
ds' :: [Der f (Fix f)]

fill :: Loc f b -> f b

fill (d,t) :: f (Fix f)

Fix (fill (d,t)) :: Fix f

-}

down :: Holey f => LocFix f -> f (LocFix f)
down (ds',Fix ts) = fmap (\ (d,t) -> (d:ds',t)) (extract ts)

{-
(ds',Fix ts) :: LocFix f
(ds',Fix ts) :: (FixC f, Fix f)
(ds',Fix ts) :: ([Der f (Fix f)], Fix f)

ds' :: [Der f (Fix f)]
Fix ts :: Fix f
ts :: f (Fix f)

extract ts :: f (Der f (Fix f), Fix f)

fmap (\ (d,t) -> (d:ds',t)) (extract ts) :: ([Der f (Fix f)], Fix f)
                                         :: (FixC f, Fix f)
                                         :: LocFix f
-}
