{-# LANGUAGE TypeOperators, EmptyDataDecls, StandaloneDeriving #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  FunctorCombo.Functor
-- Copyright   :  (c) Conal Elliott 2010
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Standard building blocks for functors
----------------------------------------------------------------------

module FunctorCombo.Functor
  (
    Const(..),Void,Unit,Id(..),inId,inId2,(:+:)(..),(:*:)(..),(:.)(..),inO,inO2,(~>)
  ) where


import Control.Applicative (Applicative(..),Const(..))

import Control.Compose (Id(..),inId,inId2,(:.)(..), inO,inO2,(~>))


-- infixl 9 :.
infixl 7 :*:
infixl 6 :+:


{--------------------------------------------------------------------
    Generic functor constructors
--------------------------------------------------------------------}

-- | Empty/zero type constructor (no inhabitants)
data Void a

-- | Unit type constructor (one inhabitant)
type Unit = Const ()

-- From Control.Compose:
-- 
--   data Id a = Id { unId :: a }

-- | Product on unary type constructors
data (f :*: g) a = f a :*: g a

-- | Sum on unary type constructors
data (f :+: g) a = L (f a) | R (g a)

-- From Control.Compose:
-- 
--   newtype (g :. f) a = O { unO :: g (f a) }


{--------------------------------------------------------------------
    Functor and Applicative instances for generic constructors
--------------------------------------------------------------------}

instance Functor Void where
  fmap _ = error "Void fmap: no void value"  -- so ghc won't complain

-- instance Functor Id where
--   fmap h (Id a) = Id (h a)

-- deriving instance Functor Id

-- instance (Functor f, Functor g) => Functor (f :+: g) where
--   fmap h (L fa) = L (fmap h fa)
--   fmap h (R ga) = R (fmap h ga)

-- i.e.,
-- 
--     fmap h . L  ==  L . fmap h
--     fmap h . R  ==  R . fmap h

deriving instance (Functor f, Functor g) => Functor (f :+: g)

-- instance (Functor f, Functor g) => Functor (f :*: g) where
--   fmap h (fa :*: ga) = fmap h fa :*: fmap h ga

-- Or:
deriving instance (Functor f, Functor g) => Functor (f :*: g)

-- TODO: Verify that the deriving instances are equivalent to the explicit versions.

-- What about Applicative instances?  I think Void could implement (<*>)
-- but not pure.  Hm.  Id and (:*:) are easy, while (:+:) is problematic.

-- instance Applicative Id where
--   pure a = Id a
--   Id f <*> Id x = Id (f x)

-- instance Applicative Id where
--   pure  = Id
--   (<*>) = inId2 ($)

instance (Applicative f, Applicative g) => Applicative (f :*: g) where
  pure a = pure a :*: pure a
  (f :*: g) <*> (a :*: b) = (f <*> a) :*: (g <*> b)

