{-# LANGUAGE DeriveFunctor, DeriveDataTypeable #-}
{-# LANGUAGE TypeOperators, TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  FunctorCombo.Pair
-- Copyright   :  (c) 2012 Conal Elliott
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Pair functor
----------------------------------------------------------------------

module FunctorCombo.Pair
  ( Pair(..)
  , fstP, sndP, swapP, fromP, toP, inP
  , firstP, secondP, zipA, unzipA, inZipA
  , curryP, uncurryP
  , preScanP, sufScanP
  ) where

-- TODO: consider using standard names like fst, snd & curry.

import Data.Monoid (Monoid(..))
import Data.Functor ((<$>))
import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..))
import Control.Applicative (Applicative(..),liftA2)
import Data.Typeable (Typeable)
import Data.Data (Data)

import FunctorCombo.Functor
import FunctorCombo.ParScan

{--------------------------------------------------------------------
    Pair functor. Just a convenience. Pair =~ Id :*: Id
--------------------------------------------------------------------}

infixl 1 :#
-- | Uniform pairs
data Pair a = a :# a deriving (Functor,Eq,Show,Typeable,Data)

-- Interpreting Pair a as Bool -> a or as Vec2 a, the instances follow
-- inevitably from the principle of type class morphisms.

-- instance Functor Pair where
--   fmap f (a :# b) = (f a :# f b)

-- The derived foldMap inserts a mempty (in GHC 7.0.4).
instance Foldable Pair where
  foldMap f (a :# b) = f a `mappend` f b

instance Applicative Pair where
  pure a = a :# a
  (f :# g) <*> (a :# b) = (f a :# g b)

instance Monad Pair where
  return = pure
  m >>= f = joinP (f <$> m)

joinP :: Pair (Pair a) -> Pair a
joinP ((a :# _) :# (_ :# d)) = a :# d

-- so
--
--   (a :# b) >>= f = (c :# d)
--    where
--      (c :# _) = f a
--      (_ :# d) = f b

instance Traversable Pair where
  traverse h (fa :# fb) = liftA2 (:#) (h fa) (h fb)
  -- sequenceA (fa :# fb) = liftA2 (:#) fa fb

instance EncodeF Pair where
  type Enc Pair = Id :*: Id
  encode (a :# b) = Id a :*: Id b
  decode (Id a :*: Id b) = a :# b

fstP, sndP :: Pair a -> a
fstP (a :# _) = a
sndP (_ :# b) = b

swapP :: Unop (Pair a)
swapP (a :# b) = b :# a

toP :: (a,a) -> Pair a
toP (a,b) = a :# b

fromP :: Pair a -> (a,a)
fromP (a :# b) = (a,b)

inP :: Unop (a,a) -> Unop (Pair a)
inP f = toP . f . fromP

firstP, secondP :: Unop a -> Unop (Pair a)
firstP  f = ((f :# id) <*>)
secondP g = ((id :# g) <*>)

-- Or use 'ap', e.g., ap (f :# id)

-- firstP  f (a :# b) = (f a :#   b)
-- secondP g (a :# b) = (  a :# g b)

zipA :: Applicative f => Pair (f a) -> f (Pair a)
zipA (u :# v) = liftA2 (:#) u v

unzipA :: Functor f => f (Pair a) -> Pair (f a)
unzipA t = fmap fstP t :# fmap sndP t

inZipA :: Applicative f => Unop (f (Pair a)) -> Unop (Pair (f a))
inZipA f = unzipA . f . zipA

-- TODO: Eliminate inZipA in favor of inDist

curryP :: (Pair a -> b) -> (a -> a -> b)
curryP g = curry (g . toP)

uncurryP :: (a -> a -> b) -> (Pair a -> b)
uncurryP f = uncurry f . fromP

preScanP :: (Functor f, Monoid o) => Pair (f o, o) -> (Pair (f o), o)
preScanP (us :# vs) = ((u :# v), vTot)
 where
   (u,uTot) = us
   (v,vTot) = preScanTweak (uTot `mappend`) vs

sufScanP :: (Functor f, Monoid o) => Pair (o, f o) -> (o, Pair (f o))
sufScanP (us :# vs) = (uTot, (u :# v))
 where
   (vTot,v) = vs
   (uTot,u) = sufScanTweak (`mappend` vTot) us


{--------------------------------------------------------------------
    A simple example: pairs
--------------------------------------------------------------------}

-- To get a first sense of generalized scans, let's use see how to scan over a
-- pair functor.

-- instance Scan Pair where
--   prefixScan (a :# b) = (mempty :# a, a `mappend` b)
--   suffixScan (a :# b) = (a `mappend` b, b :# mempty)

-- We don't really have to figure out how to define scans for every functor
-- separately. We can instead look at how functors are are composed out of their
-- essential building blocks.

instance Scan Pair where
  prefixScan = prefixScanEnc
  suffixScan = suffixScanEnc

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

-- Put somewhere standard.

-- | Unary transformation
type Unop a = a -> a
