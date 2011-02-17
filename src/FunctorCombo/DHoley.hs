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

module FunctorCombo.DHoley (Holey(..), fill) where

import Control.Arrow (first,second)

import FunctorCombo.Functor


{--------------------------------------------------------------------
    Extraction
--------------------------------------------------------------------}

-- | Location, i.e., one-hole context and a value for the hole.
type Loc f a = (Der f a, a)

-- | Alternative interface for 'fillC'.
fill :: Holey f => Loc f a -> f a
fill = uncurry fillC

class Functor f => Holey f where
  -- | Derivative, i.e., one-hole context
  type Der f :: * -> *
  -- | Fill a hole
  fillC   :: Der f a -> a -> f a
  -- | All extractions
  extract :: f a -> f (Loc f a)

-- The Functor constraint simplifies several signatures below.
instance Holey (Const x) where
  type Der (Const x) = Void
  fillC = voidF
  extract (Const x) = Const x

instance Holey Id where
  type Der Id = Unit
  fillC (Const ()) = Id
  extract (Id a) = Id (Const (), a)

instance (Holey f, Holey g) => Holey (f :+: g) where
  type Der (f :+: g) = Der f :+: Der g
  fillC (InL df) = InL . fillC df
  fillC (InR df) = InR . fillC df
  extract (InL fa) = InL ((fmap.first) InL (extract fa))
  extract (InR ga) = InR ((fmap.first) InR (extract ga))

{-

InL fa :: (f :+: g) a

fa :: f a

extract fa :: f (Loc f a)

extract fa :: f (Der f a, a)

(fmap.first) InL (extract fa) :: f ((Der f :+: Der g) a, a)

(fmap.first) InL (extract fa) :: f ((Der (f :+: g) a), a)

InL ((fmap.first) InL (extract fa)) :: (f :+: g) ((Der (f :+: g) a), a)

-}


-- Der (f :*: g) = Der f :*: g  :+:  f :*: Der g

instance (Holey f, Holey g) => Holey (f :*: g) where
  type Der (f :*: g) = Der f :*: g  :+:  f :*: Der g
  fillC (InL (dfa :*:  ga)) = (:*: ga) . fillC dfa
  fillC (InR ( fa :*: dga)) = (fa :*:) . fillC dga
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

{-
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
-}

-- Sjoerd Visscher wrote <http://conal.net/blog/posts/another-angle-on-zippers/#comment-51328>:

-- At first it was a bit disappointing that extract is so complicated for
-- functor composition, but I played a bit with the code and tweak2 can be
-- simplified (if I didn't make a mistake) to:

-- tweak2 (dgfa, fl) = (fmap.first) (O dgfa :*:) fl

-- It's interesting that (tweak2 . second extract) is very much like down!
-- Probably because Fix f is like repeated functor composition of f.

tweak2 :: Functor f => (dg (f a), f (df a, a)) -> f (((dg :. f) :*: df) a, a)
tweak2 (dgfa, fl) = (fmap.first) (O dgfa :*:) fl

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
  :: g (f (Loc (g :. f)) a)

-}

-- Der (g :.  f) = Der g :. f  :*:  Der f

instance (Holey f, Holey g) => Holey (g :. f) where
  type Der (g :.  f) = Der g :. f  :*:  Der f
  fillC (O dgfa :*: dfa) = O. fillC dgfa . fillC dfa
  extract = inO extractGF
  -- extract (O gfa) = O (extractGF gfa)


{-
O dgfa :*: dfa :: Der (g :. f) a

O dgfa :*: dfa :: (Der g :. f :*: Der f) a

dgfa :: Der g (f a)
dfa  :: Der f a

fillC dfa a :: f a

fillC dgfa (fillC dfa a) :: g (f a)

O (fillC dgfa (fillC dfa a)) :: (g :. f) a

-}
