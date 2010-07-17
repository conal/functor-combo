{-# LANGUAGE TypeOperators, TypeFamilies, UndecidableInstances, CPP
 #-}
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  FunctorCombo.MemoTrie
-- Copyright   :  (c) Conal Elliott 2010
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Functor-based memo tries (strict for now)
----------------------------------------------------------------------

module FunctorCombo.MemoTrie
  (
    HasTrie(..),memo,memo2,memo3
  ) where

import Control.Arrow (first)
import Control.Applicative ((<$>))

import qualified Data.IntTrie as IT  -- data-inttrie

import Control.Compose (result)

import FunctorCombo.Functor


{--------------------------------------------------------------------
    Class
--------------------------------------------------------------------}

infixr 0 :->:

-- | Memo trie from k to v
type k :->: v = Trie k v

-- | Domain types with associated memo tries
class HasTrie k where
    -- | Representation of trie with domain type @a@
    type Trie k :: * -> *
    -- | Create the trie for the entire domain of a function
    trie   :: (k  ->  v) -> (k :->: v)
    -- | Convert k trie to k function, i.e., access k field of the trie
    untrie :: (k :->: v) -> (k  ->  v)
    -- | List the trie elements.  Order of keys (@:: k@) is always the same.
    enumerate :: (k :->: v) -> [(k,v)]

-- -- | Domain elements of a trie
-- domain :: HasTrie a => [a]
-- domain = map fst (enumerate (trie (const oops)))
--  where
--    oops = error "Data.MemoTrie.domain: range element evaluated."


{--------------------------------------------------------------------
    Memo functions
--------------------------------------------------------------------}

-- | Trie-based function memoizer
memo :: HasTrie k => Unop (k -> v)
memo = untrie . trie

-- | Memoize a binary function, on its first argument and then on its
-- second.  Take care to exploit any partial evaluation.
memo2 :: (HasTrie s,HasTrie t) => Unop (s -> t -> a)

-- | Memoize a ternary function on successive arguments.  Take care to
-- exploit any partial evaluation.
memo3 :: (HasTrie r,HasTrie s,HasTrie t) => Unop (r -> s -> t -> a)

-- | Lift a memoizer to work with one more argument.
mup :: HasTrie t => (b -> c) -> (t -> b) -> (t -> c)
mup mem f = memo (mem . f)

memo2 = mup memo
memo3 = mup memo2

{--------------------------------------------------------------------
    Instances
--------------------------------------------------------------------}

instance HasTrie () where
  type Trie ()  = Id
  trie   f      = Id (f ())
  untrie (Id v) = const v
  enumerate (Id a) = [((),a)]

instance (HasTrie l, HasTrie r) => HasTrie (Either l r) where
  type Trie (Either l r) = Trie l :*: Trie r
  trie   f           = trie (f . Left) :*: trie (f . Right)
  untrie (tl :*: tr) = untrie tl `either` untrie tr
  enumerate (tl :*: tr) = enum' Left tl `weave` enum' Right tr

enum' :: (HasTrie a) => (a -> a') -> (a :->: b) -> [(a', b)]
enum' f = (fmap.first) f . enumerate

weave :: [a] -> [a] -> [a]
[] `weave` as = as
as `weave` [] = as
(a:as) `weave` bs = a : (bs `weave` as)


instance (HasTrie a, HasTrie b) => HasTrie (a , b) where
  type Trie (a , b) = Trie a :. Trie b
  trie   f = O (trie (trie . curry f))
  untrie (O tt) = uncurry (untrie . untrie tt)
  enumerate (O tt) =
    [ ((a,b),x) | (a,t) <- enumerate tt , (b,x) <- enumerate t ]

-- Experiment:

fToPair :: (f:*:g) a -> (f a, g a)
fToPair (fa :*: ga) = (fa,ga)

pairToF :: (f a, g a) -> (f:*:g) a
pairToF (fa,ga) = (fa :*: ga)

#define HasTrieIsomorph(Context,Type,IsoType,fromIso,toIso) \
instance Context => HasTrie (Type) where {\
  type Trie (Type) = Trie (IsoType); \
  trie f = trie (f . fromIso); \
  untrie t = untrie t . toIso; \
  enumerate = (result.fmap.first) fromIso enumerate; \
}

HasTrieIsomorph( (HasTrie (f a), HasTrie (g a))
               , (f :*: g) a, (f a,g a), pairToF, fToPair)


type BoolT = Either () ()

encodeBool :: Bool -> BoolT
encodeBool False = Left  ()
encodeBool True  = Right ()

decodeBool :: BoolT -> Bool
decodeBool (Left  ()) = False
decodeBool (Right ()) = True

HasTrieIsomorph((), Bool, BoolT, decodeBool, encodeBool)

HasTrieIsomorph((HasTrie a, HasTrie b, HasTrie c), (a,b,c), ((a,b),c)
               , (\ ((a,b),c) -> (a,b,c)), (\ (a,b,c) -> ((a,b),c)))

{-
type List' x = Either () (x,[x])

-- Hangs the compiler in ghc 6.12.1 :(
instance HasTrie x => HasTrie [x] where
    type Trie [x] = Trie (List' x)
    trie f = trie (f . list)
    untrie t = untrie t . delist
    enumerate = enum' list

list :: List' x -> [x]
list = either (const []) (uncurry (:))

delist :: [x] -> List' x
delist []     = Left ()
delist (x:xs) = Right (x,xs)
-}



enumerateEnum :: (Enum k, Num k, HasTrie k) => (k :->: v) -> [(k,v)]
enumerateEnum t = [(k, f k) | k <- [0 ..] `weave` [-1, -2 ..]]
 where
   f = untrie t

#define HasTrieIntegral(Type) \
instance HasTrie Type where { \
  type Trie Type = IT.IntTrie; \
  trie   = (<$> IT.identity); \
  untrie = IT.apply; \
  enumerate = enumerateEnum; \
}

HasTrieIntegral(Int)
HasTrieIntegral(Integer)


{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

type Unop a = a -> a



{-

{--------------------------------------------------------------------
    Testing
--------------------------------------------------------------------}

fib :: Integer -> Integer
fib m = mfib m
 where
   mfib = memo fib'
   fib' 0 = 0
   fib' 1 = 1
   fib' n = mfib (n-1) + mfib (n-2)

-- The eta-redex in fib is important to prevent a CAF.

-}
