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

module FunctorCombo.Holey (Loc,Holey(..),fill) where

import Control.Arrow (first,second)

import FunctorCombo.Functor
import FunctorCombo.Derivative


{--------------------------------------------------------------------
    Extraction
--------------------------------------------------------------------}

-- | Location, i.e., one-hole context and a value for the hole.
type Loc f a = (Der f a, a)

-- | Alternative interface for 'fillC'.
fill :: Holey f => Loc f a -> f a
fill = uncurry fillC

-- | Filling and creating one-hole contexts
class Functor f => Holey f where
  fillC    :: Der f a -> a -> f a        -- ^ Fill a hole
  extract :: f a -> f (Loc f a)         -- ^ All extractions

-- The Functor constraint simplifies several signatures below.

instance Holey (Const z) where
  fillC = voidF
  extract (Const z) = Const z

instance Holey Id where
  fillC (Const ()) = Id
  extract (Id a) = Id (Const (), a)

-- fillC (Const ()) a = Id a

-- fill (Const (), a) = Id a

instance (Holey f, Holey g) => Holey (f :+: g) where
  fillC (InL df) = InL . fillC df
  fillC (InR df) = InR . fillC df
  extract (InL fa) = InL ((fmap.first) InL (extract fa))
  extract (InR ga) = InR ((fmap.first) InR (extract ga))

-- fillC (InL df) a) = InL (fillC df a)
-- fillC (InR df) a) = InR (fillC df a)

-- fill (InL df, a) = InL (fill (df, a))
-- fill (InR df, a) = InR (fill (df, a))

--   fillC = eitherF ((result.result) InL fillC) ((result.result) InR fillC)

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
  fillC (InL (dfa :*:  ga)) = (:*: ga) . fillC dfa
  fillC (InR ( fa :*: dga)) = (fa :*:) . fillC dga
  extract (fa :*: ga) = (fmap.first) (InL . (:*: ga)) (extract fa) :*:
                        (fmap.first) (InR . (fa :*:)) (extract ga)

-- fillC (InL (dfa :*:  ga)) a = fillC dfa a :*: ga
-- fillC (InR ( fa :*: dga)) a = fa :*: fillC dga a

-- fill (InL (dfa :*:  ga), a) = fill (dfa, a) :*: ga
-- fill (InR ( fa :*: dga), a) = fa :*: fill (dga, a)


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
-- tweak2 :: Functor f => (Der g (f a), f (Loc f a)) -> f (Loc (g :. f) a)

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
  :: g (f (Loc (g :. f) a))

-}

-- Der (g :.  f) = Der g :. f  :*:  Der f

instance (Holey f, Holey g) => Holey (g :. f) where
  fillC (O dgfa :*: dfa) = O. fillC dgfa . fillC dfa
  -- fillC (O dgfa :*: dfa) a = O (fillC dgfa (fillC dfa a))
  -- extract (O gfa) = O (extractGF gfa)
  extract = inO extractGF

-- fill (O dgfa :*: dfa, a) = O (fill (dgfa, fill (dfa, a)))


{-
O dgfa :*: dfa :: Der (g :. f) a

O dgfa :*: dfa :: (Der g :. f :*: Der f) a

dgfa :: Der g (f a)
dfa  :: Der f a

fillC dfa a :: f a

fillC dgfa (fillC dfa a) :: g (f a)

O (fillC dgfa (fillC dfa a)) :: (g :. f) a

-}
