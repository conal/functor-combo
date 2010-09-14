{-# LANGUAGE StandaloneDeriving, TypeOperators, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
----------------------------------------------------------------------
-- |
-- Module      :  FunctorCombo.LubF
-- Copyright   :  (c) Conal Elliott 2010
-- License     :  GPL-3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Least upper bounds for functor combinators
----------------------------------------------------------------------

module FunctorCombo.LubF (HasLubF) where

import Data.Lub

import FunctorCombo.Functor

-- deriving instance HasLub a => HasLub (Id a)

-- Kills ghc: genDerivBinds: bad derived class lub-0.0.6:Data.Lub.HasLub{tc r3S}

-- ghc: panic! (the 'impossible' happened)
--   (GHC version 6.12.1 for i386-apple-darwin):
-- 	genDerivBinds: bad derived class lub-0.0.6:Data.Lub.HasLub{tc r3S}

{-

instance HasLub a => HasLub (Id a) where
  lub = inId2 lub

instance (HasLub a, HasLub (f a), HasLub (g a))
  => HasLub ((f :*: g) a) where
    lub = inProd2 lub

-}

{--------------------------------------------------------------------
    Functor-level lubs
--------------------------------------------------------------------}

class HasLubF f where
  lubF :: HasLub v => f v -> f v -> f v

-- instance HasLubF Id where lubF = lub

-- instance (HasLubF f, HasLubF g) => HasLubF (f :*: g) where lubF = lub

-- Could not deduce (HasLub (f v), HasLub (g v)) from the context (HasLub v)


instance HasLubF Id where lubF = inId2 lub

-- instance (HasLubF f, HasLubF g) => HasLubF (f :*: g) where lubF = inProd2 lub

-- Same error.


instance (HasLubF f, HasLubF g) => HasLubF (f :*: g) where
  (p :*: q) `lubF` (r :*: s) = (p `lubF` r) :*: (q `lubF` s)

-- TODO: Fix to match lub on pairs.  Sublety with strictness.
