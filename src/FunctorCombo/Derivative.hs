{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  FunctorCombo.Derivative
-- Copyright   :  (c) Conal Elliott 2010
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Derivatives (one-hole contexts) for standard Functor combinators
----------------------------------------------------------------------

module FunctorCombo.Derivative (Der) where

import FunctorCombo.Functor

{--------------------------------------------------------------------
    Derivatives, i.e., one-hole contexts
--------------------------------------------------------------------}

-- | A derivative, i.e., a one-hole context for a container f (probably a functor).
type family Der (f :: (* -> *)) :: (* -> *)

type instance Der (Const a) = Void

type instance Der Id = Unit

type instance Der (f :+: g) = Der f :+: Der g

type instance Der (f :*: g) = Der f :*: g  :+:  f :*: Der g

type instance Der (g :.  f) = Der g :. f  :*:  Der f

