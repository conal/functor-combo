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
-- 
-- Warning: this formulation cannot handle recursive types.
-- The type checker fails to terminate.  Wondering about solutions.
----------------------------------------------------------------------

module FunctorCombo.MemoTrie
  (
    HasTrie(..),memo,memo2,memo3
  ) where

import Control.Arrow (first)
import Control.Applicative ((<$>))

import qualified Data.IntTrie as IT  -- data-inttrie
import Data.Tree

import Control.Compose (result)

import FunctorCombo.Functor
import FunctorCombo.Regular


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

#define HasTrieIsomorph(Context,Type,IsoType,toIso,fromIso) \
instance Context => HasTrie (Type) where {\
  type Trie (Type) = Trie (IsoType); \
  trie f = trie (f . (fromIso)); \
  untrie t = untrie t . (toIso); \
  enumerate = (result.fmap.first) (fromIso) enumerate; \
}

HasTrieIsomorph( HasTrie a, Const a x, a, getConst, Const )


HasTrieIsomorph( HasTrie a, Id a, a, unId, Id )

HasTrieIsomorph( (HasTrie (f a), HasTrie (g a))
               , (f :*: g) a, (f a,g a)
               , \ (fa :*: ga) -> (fa,ga), \ (fa,ga) -> (fa :*: ga) )

HasTrieIsomorph( (HasTrie (f a), HasTrie (g a))
               , (f :+: g) a, Either (f a) (g a)
               , eitherF Left Right, either L R )


HasTrieIsomorph( (), Bool, Either () ()
               , bool (Left ()) (Right ())
               , either (\ () -> False) (\ () -> True))

HasTrieIsomorph((HasTrie a, HasTrie b, HasTrie c), (a,b,c), ((a,b),c)
               , \ (a,b,c) -> ((a,b),c), \ ((a,b),c) -> (a,b,c))

HasTrieIsomorph((HasTrie a, HasTrie b, HasTrie c, HasTrie d)
               , (a,b,c,d), ((a,b,c),d)
               , \ (a,b,c,d) -> ((a,b,c),d), \ ((a,b,c),d) -> (a,b,c,d))


-- #define HasTrieRegular(Context,Type) \
-- HasTrieIsomorph(Context, Type, PF (Type) (Type) , unwrap, wrap)

-- #define HasTrieRegular1(TypeCon) \
-- HasTrieRegular(HasTrie a, TypeCon a)

-- Hangs ghc 6.12.1:
-- 
-- HasTrieRegular(HasTrie a, [a])
-- HasTrieRegular(HasTrie a, Tree a)

-- HasTrieRegular1([])
-- HasTrieRegular1(Tree)

-- I think the problem is infinite types.  Try an explicit newtype to
-- break the cycle.


-- newtype ListTrie a v = ListTrie (Trie (PF [a] [a]) v)
 
-- instance HasTrie a => HasTrie [a] where
--   type Trie [a] = ListTrie a
--   trie f = ListTrie (trie (f . wrap))
--   untrie (ListTrie t) = untrie t . unwrap
--   enumerate (ListTrie t) = (result.fmap.first) wrap enumerate $ t

-- Works.  Now abstract into a macro

#define HasTrieRegular(Context,Type,TrieType,TrieCon) \
newtype TrieType v = TrieCon (Trie (PF (Type) (Type)) v); \
instance Context => HasTrie (Type) where { \
  type Trie (Type) = TrieType; \
  trie f = TrieCon (trie (f . wrap)); \
  untrie (TrieCon t) = untrie t . unwrap; \
  enumerate (TrieCon t) = (result.fmap.first) wrap enumerate $ t; \
}

-- For instance,

-- HasTrieRegular(HasTrie a, [a] , ListTrie a, ListTrie)
-- HasTrieRegular(HasTrie a, Tree, TreeTrie a, TreeTrie)

-- Simplify a bit with a macro for unary regular types.
-- Make similar defs for binary etc as needed.

#define HasTrieRegular1(TypeCon,TrieCon) \
HasTrieRegular(HasTrie a, TypeCon a, TrieCon a, TrieCon)

HasTrieRegular1([]  , ListTrie)
HasTrieRegular1(Tree, TreeTrie)



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

bool :: a -> a -> Bool -> a
bool t e b = if b then t else e

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
