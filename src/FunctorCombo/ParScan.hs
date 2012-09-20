{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  FunctorCombo.ParScan
-- Copyright   :  (c) 2012 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Composable parallel scanning from
-- <http://conal.net/blog/posts/composable-parallel-scanning/>
----------------------------------------------------------------------

module FunctorCombo.ParScan
  ( Scan(..), PreScanO, SufScanO
  , prefixScanEnc, suffixScanEnc
  , preScanTweak, sufScanTweak
  , prefixSums, suffixSums
  ) where

-- TODO: explicit exports

import Prelude hiding (zip,unzip)

import Data.Monoid (Monoid(..),Sum(..))
import Control.Applicative (Applicative(..),liftA2,(<$>))
import Control.Arrow ((&&&),(***),first,second)
import Data.Foldable
import Data.Traversable

import FunctorCombo.Functor

type PreScanO f a = (f a, a)
type SufScanO f a = (a, f a)

-- | Parallel scans. `prefixScan` accumulates moving left-to-right, while
-- `suffixScan` accumulates moving right-to-left.
class Scan f where
  prefixScan :: Monoid m => f m -> PreScanO f m
  suffixScan :: Monoid m => f m -> SufScanO f m

{--------------------------------------------------------------------
    Functor combinators
--------------------------------------------------------------------}

-- The constant functor is easiest. There are no values to accumulate, so the
-- final result (fold) is `mempty`.

instance Scan (Const x) where
  prefixScan (Const x) = (Const x, mempty)
  suffixScan (Const x) = (mempty, Const x)


instance Scan Id where
  prefixScan (Id m) = (Id mempty, m)
  suffixScan (Id m) = (m, Id mempty)

instance (Scan f, Scan g) => Scan (f :+: g) where
  prefixScan (InL fa) = first  InL (prefixScan fa)
  prefixScan (InR ga) = first  InR (prefixScan ga)
  
  suffixScan (InL fa) = second InL (suffixScan fa)
  suffixScan (InR ga) = second InR (suffixScan ga)

-- These definitions correspond to simple "commutative diagram" properties,
-- e.g.,

-- prefixScan . InL == second InL . prefixScan

-- Product scannning is a little trickier. Scan each of the two parts
-- separately, and then combine the final (`fold`) part of one result with each
-- of the non-final elements of the other.

preScanTweak :: Functor f => (a -> b) -> PreScanO f a -> PreScanO f b
preScanTweak h = fmap h *** h

sufScanTweak :: Functor f => (a -> b) -> SufScanO f a -> SufScanO f b
sufScanTweak h = h *** fmap h

-- preScanTweak h (fa,a) = (h <$> fa, h a)
-- sufScanTweak h (a,fa) = (h a, h <$> fa)

-- TODO: Maybe make PreScanO and SufScanO into data types, and replace
-- preScanTweak and sufScanTweak with fmap.
--
--   data PreScanO' f a = f a :> a deriving Functor
--   data SufScanO' f a = a :< f a deriving Functor

instance (Scan f, Scan g, Functor f, Functor g) => Scan (f :*: g) where

--   prefixScan (fa :*: ga) = (fa' :*: ga', ag)
--    where (fa',af) = prefixScan fa
--          (ga',ag) = preScanTweak (af `mappend`) (prefixScan ga)

  prefixScan = first asProd
             . assocL
             . second tweak
             . assocR
             . (prefixScan *** prefixScan)
             . asPair
   where
     tweak (af,w) = preScanTweak (af `mappend`) w

--   suffixScan (fa :*: ga) = (af, fa' :*: ga')
--    where (ag,ga') = suffixScan ga
--          (af,fa') = sufScanTweak (`mappend` ag) (suffixScan fa)

  suffixScan = second asProd
             . assocR
             . first tweak
             . assocL
             . (suffixScan *** suffixScan)
             . asPair
   where
     tweak (w,ag) = sufScanTweak (`mappend` ag) w


-- Note that Functor f above is for suffixScan, and Functor g for prefixScan.
-- If we split into two classes, we'd get a bit more generality.

-- Finally, composition is the trickiest. The target signatures:
-- 
--   prefixScan :: Monoid m => (g :. f) m -> ((g :. f) m, m)
--   suffixScan :: Monoid m => (g :. f) m -> (m, (g :. f) m)

-- To find the prefix and suffix scan definitions, fiddle with types beginning
-- at the domain type for `prefixScan` or `suffixScan` and arriving at the range
-- type.

-- Some helpers:

zip :: Applicative g => (g a, g b) -> g (a,b)
zip = uncurry (liftA2 (,))

unzip :: Functor g => g (a,b) -> (g a, g b)
unzip = fmap fst &&& fmap snd

assocL :: (a,(b,c)) -> ((a,b),c)
assocL    (a,(b,c)) =  ((a,b),c)

assocR :: ((a,b),c) -> (a,(b,c))
assocR   ((a,b),c) =  (a,(b,c))

adjustL :: (Functor f, Monoid m) => (f m, m) -> f m
adjustL (ms, m) = (m `mappend`) <$> ms

adjustR :: (Functor f, Monoid m) => (m, f m) -> f m
adjustR (m, ms) = (`mappend` m) <$> ms

-- TODO: Reconsider names 'adjustL' and 'adjustR'

-- First `prefixScan`:

-- < gofm                     :: (g :. f) m
-- < unO                   '' :: g (f m)
-- < fmap prefixScan       '' :: g (f m, m)
-- < unzip                 '' :: (g (f m), g m)
-- < second prefixScan     '' :: (g (f m), (g m, m))
-- < assocL                '' :: ((g (f m), g m), m)
-- < first  zip            '' :: (g (f m, m), m)
-- < first  (fmap adjustL) '' :: (g (f m), m)
-- < first  O              '' :: ((g :. f) m, m)

-- Then `suffixScan`:

-- < gofm                     :: (g :. f) m
-- < unO                   '' :: g (f m)
-- < fmap suffixScan       '' :: g (m, f m)
-- < unzip                 '' :: (g m, g (f m))
-- < first  suffixScan     '' :: ((m, g m), g (f m))
-- < assocR                '' :: (m, (g m, g (f m)))
-- < second zip            '' :: (m, (g (m, f m)))
-- < second (fmap adjustR) '' :: (m, (g (f m)))
-- < second O              '' :: (m, ((g :. f) m))

-- Putting together the pieces and simplifying just a bit leads to the method
-- definitions:

instance (Scan g, Scan f, Functor f, Applicative g) => Scan (g :. f) where
  prefixScan = first (O . fmap adjustL . zip)
             . assocL
             . second prefixScan
             . unzip
             . fmap prefixScan
             . unO
  
  suffixScan = second (O . fmap adjustR . zip)
             . assocR
             . first  suffixScan
             . unzip
             . fmap suffixScan
             . unO

prefixScanEnc :: (EncodeF f, Scan (Enc f), Monoid m) => f m -> PreScanO f m
prefixScanEnc = first  decode . prefixScan . encode

suffixScanEnc :: (EncodeF f, Scan (Enc f), Monoid m) => f m -> SufScanO f m
suffixScanEnc = second decode . suffixScan . encode

prefixSums :: (Functor f, Scan f, Num a) => f a -> PreScanO f a
prefixSums = preScanTweak getSum . prefixScan . fmap Sum

suffixSums :: (Functor f, Scan f, Num a) => f a -> SufScanO f a
suffixSums = sufScanTweak getSum . suffixScan . fmap Sum
