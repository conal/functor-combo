{-# LANGUAGE TypeFamilies, TypeOperators, TupleSections #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  FunctorCombo.Holey
-- Copyright   :  (c) Conal Elliott 2010
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Filling and extracting derivatives (one-hole contexts)
----------------------------------------------------------------------

module FunctorCombo.Holey (Holey(..)) where

import Control.Arrow (first,second)

import FunctorCombo.Functor
import FunctorCombo.Derivative


{--------------------------------------------------------------------
    Extraction
--------------------------------------------------------------------}

class Functor f => Holey f where
  fill    :: Loc f a -> f a
  extract :: f a -> f (Loc f a)

-- The Functor constraint simplifies several signatures below.

instance Holey (Const z) where
  fill = error "fill for Const z: no Der values"
  extract (Const z) = Const z

instance Holey Id where
  fill (Const (), a) = Id a
  extract (Id a) = Id (Const (), a)

instance (Holey f, Holey g) => Holey (f :+: g) where
  fill (L df, a) = L (fill (df, a))
  fill (R df, a) = R (fill (df, a))
  extract (L fa) = L ((fmap.first) L (extract fa))
  extract (R ga) = R ((fmap.first) R (extract ga))

{-

L fa :: (f :+: g) a

fa :: f a

extract fa :: f (Loc f a)

(fmap.first) L (extract fa) :: f ((Der f :+: Der g) a, a)

(fmap.first) L (extract fa) :: f ((Der (f :+: g) a), a)

L ((fmap.first) L (extract fa)) :: (f :+: g) ((Der (f :+: g) a), a)

-}


-- Der (f :*: g) = Der f :*: g  :+:  f :*: Der g

instance (Holey f, Holey g) => Holey (f :*: g) where
  fill (L (dfa :*:  ga), a) = fill (dfa, a) :*: ga
  fill (R ( fa :*: dga), a) = fa :*: fill (dga, a)
  extract (fa :*: ga) = (fmap.first) (L . (:*: ga)) (extract fa) :*:
                        (fmap.first) (R . (fa :*:)) (extract ga)

{-

fa :*: ga :: (f :*: g) a

fa :: f a

extract fa :: f (Loc f a)

(fmap.first) (:*: ga) (extract fa) :: f ((Der f :*: g) a, a)

(fmap.first) (L . (:*: ga)) (extract fa)
  :: f (((Der f :*: g) :+: (f :*: Der g)) a, a)

(fmap.first) (L . (:*: ga)) (extract fa) :: f ((Der (f :*: g)) a, a)

(fmap.first) (R . (fa :*:)) (extract ga) :: g ((Der (f :*: g)) a, a)


(fmap.first) (L . (:*: ga)) (extract fa) :*: (fmap.first) (R . (fa :*:)) (extract ga)
  :: (f :*: g) (Der (f :*: g) a, a)

-}

-- type instance Der (g :.  f) = Der g :. f  :*:  Der f


lassoc :: (p,(q,r)) -> ((p,q),r)
lassoc    (p,(q,r)) =  ((p,q),r)

squishP :: Functor f => (a, f b) -> f (a,b)
squishP (a,fb) = fmap (a,) fb

tweak1 :: Functor f => (dg (fa), f (dfa, a)) -> f ((dg (fa), dfa), a)
tweak1 = fmap lassoc . squishP

chainRule :: (dg (f a), df a) -> ((dg :. f) :*: df) a
chainRule (dgfa, dfa) = O dgfa :*: dfa

tweak2 :: Functor f => (dg (f a), f (df a, a)) -> f (((dg :. f) :*: df) a, a)
tweak2 = (fmap.first) chainRule . tweak1

-- And more specifically,
-- 
-- tweak2 :: Functor f => (Der g (f a), f (Loc f a)) -> f (((Der g :. f) :*: Der f) a, a)
-- tweak2 :: Functor f => (Der g (f a), f (Loc f a)) -> f (Der (g :. f) a, a)

{-
(dg fa, f (dfa,a))

f (dg fa, (df,a))

f ((dg fa, dfa), a)
-}

extractGF :: (Holey f, Holey g) =>
             g (f a) -> g (f (Loc (g :. f) a))
extractGF = fmap (tweak2 . second extract) . extract

{-

gfa :: g (f a)

extract gfa :: g (Der g (f a), f a)

fmap (second extract) (extract gfa) :: g (Der g (f a), f (Loc f a))

fmap (tweak2 . second extract) (extract gfa) 
  :: g (f ((Der (g :. f :*: Der f) a), a))

-}

-- Der (g :.  f) = Der g :. f  :*:  Der f

instance (Holey f, Holey g) => Holey (g :. f) where
  -- fill (O dgfa :*: dfa) = O . fill dgfa . fill dfa
  fill (O dgfa :*: dfa, a) = O (fill (dgfa, fill (dfa, a)))
  -- extract (O gfa) = O (extractGF gfa)
  extract = inO extractGF


{-
O dgfa :*: dfa :: Der (g :. f) a

O dgfa :*: dfa :: (Der g :. f :*: Der f) a

dgfa :: Der g (f a)
dfa  :: Der f a

fill dfa a :: f a

fill dgfa (fill dfa a) :: g (f a)

O (fill dgfa (fill dfa a)) :: (g :. f) a

-}
