{-# LANGUAGE TypeOperators, EmptyDataDecls #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  FunctorCombo.Functor
-- Copyright   :  (c) Conal Elliott 2010
-- License     :  GPL-3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Standard building blocks for functors
----------------------------------------------------------------------

module FunctorCombo.Functor
  (
    Consta,Void,Unit,Id(..),inId,(:+:)(..),(:*:)(..),(:.)(..),inO,(~>)
  ) where


import Control.Applicative (Const)

import Control.Compose (Id(..),inId,(:.)(..), inO,(~>))


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
