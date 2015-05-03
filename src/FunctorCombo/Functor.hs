{-# LANGUAGE TypeOperators, EmptyDataDecls, StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TypeFamilies, CPP #-}

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
    Const(..),Void,voidF,Unit,unit,Id(..),unId,inId,inId2
  , (:+:)(..),eitherF
  , (:*:)(..),asProd,asPair,fstF,sndF
  , (:.)(..),unO,inO,inO2,(~>),(<~)
  , Lift(..), (:*:!)(..), (:+:!)(..), eitherF'
  , pairF, unPairF, inProd, inProd2
  , EncodeF(..)
  ) where


import Data.Orphans ()
import Data.Monoid (Monoid(..))
import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..))
import Control.Applicative (Applicative(..),Const(..),liftA2,(<$>))
import Control.Monad (join)

import Control.Compose (Id(..),unId,inId,inId2,(:.)(..),unO,inO,inO2,(~>),(<~))

-- infixl 9 :.
infixl 7 :*:
infixl 6 :+:


{--------------------------------------------------------------------
    Generic functor constructors
--------------------------------------------------------------------}

-- | Empty/zero type constructor (no inhabitants)
data Void a

voidF :: Void a -> b
voidF = error "voidF: no value of type Void"


-- | Unit type constructor (one inhabitant)
type Unit = Const ()

-- | The unit value
unit :: Unit ()
unit = Const ()

-- From Control.Compose:
-- 
--   newtype Id a = Id a

-- | Product on unary type constructors
data (f :*: g) a = f a :*: g a deriving (Show,Functor)

asPair :: (f :*: g) a -> (f a, g a)
asPair (fa :*: ga) = (fa,ga)

asProd :: (f a, g a) -> (f :*: g) a
asProd (fa,ga) = (fa :*: ga)

-- | Like 'fst'
fstF :: (f :*: g) a -> f a
fstF (fa :*: _) = fa

-- | Like 'snd'
sndF :: (f :*: g) a -> g a
sndF (_ :*: ga) = ga

-- | Sum on unary type constructors
data (f :+: g) a = InL (f a) | InR (g a) deriving (Show,Functor)

eitherF :: (f a -> b) -> (g a -> b) -> (f :+: g) a -> b
eitherF p _ (InL fa) = p fa
eitherF _ q (InR ga) = q ga

-- From Control.Compose:
-- 
--   newtype (g :. f) a = O (g (f a))


{--------------------------------------------------------------------
    Instances
--------------------------------------------------------------------}

instance Functor Void where
  fmap _ = error "Void fmap: no void value"  -- so ghc won't complain

-- deriving instance Functor Void
-- 
-- Leads to
-- 
-- ghc: panic! (the 'impossible' happened)
--   (GHC version 6.12.1 for i386-apple-darwin):
-- 	TcPat.checkArgs
-- 
-- See ticket <http://hackage.haskell.org/trac/ghc/ticket/4220>.
-- 
-- TODO: replace explicit definition with deriving, when the compiler fix
-- has been around for a while.

-- instance Foldable (Const b) where
--   -- fold (Const _) = mempty
--   foldMap _ (Const _) = mempty

-- instance Traversable (Const b) where
--   -- sequenceA (Const b) = pure (Const b)
--   traverse _ (Const b) = pure (Const b)

-- instance Functor Id where
--   fmap h (Id a) = Id (h a)

-- deriving instance Functor Id

-- instance (Functor f, Functor g) => Functor (f :+: g) where
--   fmap h (InL fa) = InL (fmap h fa)
--   fmap h (InR ga) = InR (fmap h ga)

-- i.e.,
-- 
--     fmap h . InL  ==  InL . fmap h
--     fmap h . InR  ==  InR . fmap h

-- deriving instance (Functor f, Functor g) => Functor (f :+: g)

-- instance (Functor f, Functor g) => Functor (f :*: g) where
--   fmap h (fa :*: ga) = fmap h fa :*: fmap h ga

-- Or:
-- deriving instance (Functor f, Functor g) => Functor (f :*: g)

-- TODO: Verify that the deriving instances are equivalent to the explicit versions.

instance (Foldable f, Foldable g) => Foldable (f :+: g) where
  -- fold (InL fa) = fold fa
  -- fold (InR ga) = fold ga
  fold = eitherF fold fold
  -- foldMap p (InL fa) = foldMap p fa
  -- foldMap p (InR ga) = foldMap p ga
  foldMap p = eitherF (foldMap p) (foldMap p)

instance (Traversable f, Traversable g) => Traversable (f :+: g) where
  -- sequenceA (InL fa) = InL <$> sequenceA fa
  -- sequenceA (InR ga) = InR <$> sequenceA ga
  sequenceA = eitherF (fmap InL . sequenceA) (fmap InR . sequenceA)
  -- traverse p (InL fa) = InL <$> traverse p fa
  -- traverse p (InR ga) = InR <$> traverse p ga
  traverse p = eitherF (fmap InL . traverse p) (fmap InR . traverse p)


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

instance (Functor f, Functor g, Monad f, Monad g) =>
         Monad (f :*: g) where
  return a = return a :*: return a
  m >>= k = joinP (k <$> m)

joinP :: (Functor f, Functor g, Monad f, Monad g) =>
         (f :*: g) ((f :*: g) a) -> (f :*: g) a
joinP m = join (fstF <$> fstF m) :*: join (sndF <$> sndF m)

-- joinP (ffga :*: gfga) = join (fstF <$> ffga) :*: join (sndF <$> gfga)



instance (Foldable f, Foldable g) => Foldable (f :*: g) where
  -- fold (fa :*: ga) = fold fa `mappend` fold ga
  -- fold q = fold (fstF q) `mappend` fold (sndF q)
  -- fold = (fold . fstF) `mappend` (fold . sndF) -- function monoid
  foldMap p (fa :*: ga) = foldMap p fa `mappend` foldMap p ga


instance (Traversable f, Traversable g) => Traversable (f :*: g) where
  -- sequenceA (fha :*: gha) = liftA2 (:*:) (sequenceA fha) (sequenceA gha)
  traverse p (fha :*: gha) = liftA2 (:*:) (traverse p fha) (traverse p gha)

-- instance (Applicative f, Applicative g) => Applicative (f :+: g) where
--   -- pure = ?? -- could use either 'InL . pure' or 'InR . pure'
--   InL f <*> InL a = InL (f <*> a)
--   InR g <*> InR b = InR (g <*> b)
--   _ <*> _ = error "(<*>) on f :+: g: structural mismatch"

-- instance (Functor g, Functor f) => Functor (g :. f) where
--   fmap = inO.fmap.fmap

-- or

-- deriving instance (Functor g, Functor f) => Functor (g :. f)


{--------------------------------------------------------------------
    Some handy structural manipulators
--------------------------------------------------------------------}

pairF :: (f a, g a) -> (f :*: g) a
pairF (fa , ga) = (fa :*: ga)

-- pairF = uncurry (:*:)

unPairF :: (f :*: g) a -> (f a, g a)
unPairF (fa :*: ga) = (fa , ga)

-- Could also define curryF, uncurryF

inProd :: ((f a , g a) -> (h b , i b)) -> ((f :*: g) a -> (h :*: i) b)
inProd = pairF <~ unPairF


inProd2 :: ((f a , g a) -> (h b , i b) -> (j c , k c))
        -> ((f :*: g) a -> (h :*: i) b -> (j :*: k) c)
inProd2 = inProd <~ unPairF


{--------------------------------------------------------------------
    Explicit non-strictness
--------------------------------------------------------------------}

-- Idea: make all non-strictness explicit via unlifted product & sums,
-- and explicit lifting.  Note that Id and Const are already strict.

-- | Add a bottom to a type
data Lift a = Lift { unLift :: a } deriving Functor

infixl 6 :+:!
infixl 7 :*:!

-- | Strict product functor

-- data (f :*:! g) a = (:*:!) { pfst :: !(f a), psnd :: !(g a) } deriving Functor

data (f :*:! g) a = !(f a) :*:! !(g a) deriving Functor

-- pfst :: (f :*:! g) a -> f a
-- pfst (fa :*:! _) = fa

-- psnd :: (f :*:! g) a -> g a
-- psnd (_ :*:! ga) = ga

-- t1 :: Id Int
-- t1 = psnd (undefined :*:! Id 3)   -- *** Id Exception: Prelude.undefined

-- t1 :: Id Int
-- t1 = x where x :*:! _ = undefined :*:! Id 3   -- *** Id Exception: Prelude.undefined

-- | Strict sum functor
data (f :+:! g) a = InL' !(f a) | InR' !(g a) deriving Functor

-- | Case analysis on strict sum functor
eitherF' :: (f a -> c) -> (g a -> c) -> ((f :+:! g) a -> c)
eitherF' p _ (InL' fa) = p fa
eitherF' _ q (InR' ga) = q ga

{--------------------------------------------------------------------
    Encoding via standard functor combinators
--------------------------------------------------------------------}

class EncodeF f where
  type Enc f :: * -> *
  encode :: f a -> Enc f a
  decode :: Enc f a -> f a

-- TODO: Very similar to the Regular class. Can they be reconciled?
