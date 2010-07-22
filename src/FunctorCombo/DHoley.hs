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
                                                         
-- Variation on Holey, integrating 'Der'
----------------------------------------------------------------------

module FunctorCombo.DHoley (Holey(..)) where

import Control.Arrow (first,second)

import FunctorCombo.Functor


{--------------------------------------------------------------------
    Extraction
--------------------------------------------------------------------}

-- | Location, i.e., one-hole context and a value for the hole.
type Loc f a = (Der f a, a)

class Functor f => Holey f where
  -- | Derivative, i.e., one-hole context
  type Der f :: * -> *
  -- | Fill a hole
  fill    :: Loc f a -> f a
  -- | All extractions
  extract :: f a -> f (Loc f a)

-- The Functor constraint simplifies several signatures below.
instance Holey (Const z) where
  type Der (Const z) = Void
  fill = error "fill for Const z: no Der values"
  extract (Const z) = Const z

instance Holey Id where
  type Der Id = Unit
  fill (Const (), a) = Id a
  extract (Id a) = Id (Const (), a)

instance (Holey f, Holey g) => Holey (f :+: g) where
  type Der (f :+: g) = Der f :+: Der g
  fill (InL df, a) = InL (fill (df, a))
  fill (InR df, a) = InR (fill (df, a))
  extract (InL fa) = InL ((fmap.first) InL (extract fa))
  extract (InR ga) = InR ((fmap.first) InR (extract ga))

{-

InL fa :: (f :+: g) a

fa :: f a

extract fa :: f (Loc f a)

(fmap.first) InL (extract fa) :: f ((Der f :+: Der g) a, a)

(fmap.first) InL (extract fa) :: f ((Der (f :+: g) a), a)

InL ((fmap.first) InL (extract fa)) :: (f :+: g) ((Der (f :+: g) a), a)

-}


-- Der (f :*: g) = Der f :*: g  :+:  f :*: Der g

instance (Holey f, Holey g) => Holey (f :*: g) where
  type Der (f :*: g) = Der f :*: g  :+:  f :*: Der g
  fill (InL (dfa :*:  ga), a) = fill (dfa, a) :*: ga
  fill (InR ( fa :*: dga), a) = fa :*: fill (dga, a)
  extract (fa :*: ga) = (fmap.first) (InL . (:*: ga)) (extract fa) :*:
                        (fmap.first) (InR . (fa :*:)) (extract ga)

{-

fa :*: ga :: (f :*: g) a

fa :: f a

extract fa :: f (Loc f a)

(fmap.first) (:*: ga) (extract fa) :: f ((Der f :*: g) a, a)

(fmap.first) (InL . (:*: ga)) (extract fa)
  :: f (((Der f :*: g) :+: (f :*: Der g)) a, a)

(fmap.first) (InL . (:*: ga)) (extract fa) :: f ((Der (f :*: g)) a, a)

(fmap.first) (InR . (fa :*:)) (extract ga) :: g ((Der (f :*: g)) a, a)


(fmap.first) (InL . (:*: ga)) (extract fa) :*: (fmap.first) (InR . (fa :*:)) (extract ga)
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
  type Der (g :.  f) = Der g :. f  :*:  Der f
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
