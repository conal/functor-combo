{-# LANGUAGE TypeOperators, TypeFamilies, UndecidableInstances, CPP
 #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-unused-imports #-}  -- temporary while testing
----------------------------------------------------------------------
-- |
-- Module      :  FunctorCombo.MemoTrie
-- Copyright   :  (c) Conal Elliott 2010
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Functor-based memo tries
-- 
----------------------------------------------------------------------

module FunctorCombo.MemoTrie
  (
    HasTrie(..),memo,memo2,memo3
  ) where

-- I think this module has split into StrictMemo and NonstrictMemo

#define NonstrictMemo

import Control.Arrow (first)
import Control.Applicative ((<$>))

import qualified Data.IntTrie as IT  -- data-inttrie
import Data.Tree

import Control.Compose (result)  -- TypeCompose

#ifdef NonstrictMemo
import Data.Lub
#endif

import FunctorCombo.Functor
import FunctorCombo.Regular


{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

type Unop a = a -> a

bool :: a -> a -> Bool -> a
bool t e b = if b then t else e


{--------------------------------------------------------------------
    Class
--------------------------------------------------------------------}

infixr 0 :->:

#ifdef NonstrictMemo
data Trie k v = Trie v (STrie k v)

type k :->: v = Trie k v

-- Bottom
bottom :: a
bottom = error "MemoTrie: evaluated bottom.  Oops!"

-- | Create the trie for the entire domain of a function
trie   :: HasLub(v) => HasTrie k => (k  ->  v) -> (k :->: v)
trie f = Trie (f bottom) (sTrie f)

-- | Convert k trie to k function, i.e., access k field of the trie
untrie :: HasLub(v) => HasTrie k => (k :->: v) -> (k  ->  v)
untrie (Trie b t) = const b `lub` sUntrie t

#else
type Trie k = STrie k

type k :->: v = k :-> v

-- Bogus HasLub constraint
#define HasLub(v) ()

trie   :: HasTrie k => (k  ->  v) -> (k :->: v)
trie = sTrie

untrie :: HasTrie k => (k :->: v) -> (k  ->  v)
untrie = sUntrie

#endif

-- | Memo trie from k to v
type k :-> v = STrie k v

-- | Domain types with associated memo tries
class HasTrie k where
    -- | Representation of trie with domain type @a@
    type STrie k :: * -> *
    -- | Create the trie for the entire domain of a function
    sTrie   :: HasLub(v) => (k  ->  v) -> (k :-> v)
    -- | Convert k trie to k function, i.e., access k field of the trie
    sUntrie :: HasLub(v) => (k :-> v) -> (k  ->  v)

--     -- | List the trie elements.  Order of keys (@:: k@) is always the same.
--     enumerate :: HasLub(v) => (k :-> v) -> [(k,v)]

-- -- | Domain elements of a trie
-- domain :: HasTrie a => [a]
-- domain = map fst (enumerate (trie (const oops)))
--  where
--    oops = error "Data.MemoTrie.domain: range element evaluated."


-- TODO: what about enumerate and strict/nonstrict?


{--------------------------------------------------------------------
    Memo functions
--------------------------------------------------------------------}

-- | Trie-based function memoizer
memo :: HasLub(v) => HasTrie k => Unop (k -> v)
memo = untrie . trie

-- | Memoize a binary function, on its first argument and then on its
-- second.  Take care to exploit any partial evaluation.
memo2 :: HasLub(a) => (HasTrie s,HasTrie t) => Unop (s -> t -> a)

-- | Memoize a ternary function on successive arguments.  Take care to
-- exploit any partial evaluation.
memo3 :: HasLub(a) => (HasTrie r,HasTrie s,HasTrie t) => Unop (r -> s -> t -> a)

-- | Lift a memoizer to work with one more argument.
mup :: HasLub(c) => HasTrie t => (b -> c) -> (t -> b) -> (t -> c)
mup mem f = memo (mem . f)

memo2 = mup memo
memo3 = mup memo2

{--------------------------------------------------------------------
    Instances
--------------------------------------------------------------------}

instance HasTrie () where
  type STrie ()  = Id
  sTrie   f      = Id (f ())
  sUntrie (Id v) = const v
--   enumerate (Id a) = [((),a)]

instance (HasTrie a, HasTrie b) => HasTrie (Either a b) where
  type STrie (Either a b) = Trie a :*: Trie b
  sTrie   f           = trie (f . Left) :*: trie (f . Right)
  sUntrie (ta :*: tb) = untrie ta `either` untrie tb
--   enumerate (ta :*: tb) = enum' Left ta `weave` enum' Right tb

-- enum' :: HasLub(b) => HasTrie a => (a -> a') -> (a :->: b) -> [(a', b)]
-- enum' f = (fmap.first) f . enumerate

-- weave :: [a] -> [a] -> [a]
-- [] `weave` as = as
-- as `weave` [] = as
-- (a:as) `weave` bs = a : (bs `weave` as)

-- To do: rethink enumerate and come back to it.  How might enumeration
-- work in the presence of nonstrict memo tries?  Maybe lub the
-- approximation into each of the values enumerated from the strict memo tries.
-- Would it help any??

instance (HasTrie a, HasTrie b) => HasTrie (a , b) where
  type STrie (a , b) = Trie a :. Trie b
  sTrie   f = O (trie (trie . curry f))
  sUntrie (O tt) = uncurry (untrie . untrie tt)
--   enumerate (O tt) =
--     [ ((a,b),x) | (a,t) <- enumerate tt , (b,x) <- enumerate t ]

-- Oops:
-- 
--     Could not deduce (HasLub (Trie b v)) from the context (HasLub v)
--       arising from a use of `trie'
-- 
--     Could not deduce (HasLub (Trie b v)) from the context (HasLub v)
--       arising from a use of `untrie'

-- Eep.  How to fix this one?

{-


#define HasTrieIsomorph(Context,Type,IsoType,toIso,fromIso) \
instance Context => HasTrie (Type) where { \
  type STrie (Type) = Trie (IsoType); \
  sTrie f = sTrie (f . (fromIso)); \
  sUntrie t = sUntrie t . (toIso); \
  enumerate = (result.fmap.first) (fromIso) enumerate; \
}


HasTrieIsomorph( (), Bool, Either () ()
               , bool (Left ()) (Right ())
               , either (\ () -> True) (\ () -> False))

HasTrieIsomorph((HasTrie a, HasTrie b, HasTrie c), (a,b,c), ((a,b),c)
               , \ (a,b,c) -> ((a,b),c), \ ((a,b),c) -> (a,b,c))

HasTrieIsomorph((HasTrie a, HasTrie b, HasTrie c, HasTrie d)
               , (a,b,c,d), ((a,b,c),d)
               , \ (a,b,c,d) -> ((a,b,c),d), \ ((a,b,c),d) -> (a,b,c,d))


-- As well as the functor combinators themselves

HasTrieIsomorph( HasTrie x, Const x a, x, getConst, Const )

HasTrieIsomorph( HasTrie a, Id a, a, unId, Id )

HasTrieIsomorph( (HasTrie (f a), HasTrie (g a))
               , (f :*: g) a, (f a,g a)
               , \ (fa :*: ga) -> (fa,ga), \ (fa,ga) -> (fa :*: ga) )

HasTrieIsomorph( (HasTrie (f a), HasTrie (g a))
               , (f :+: g) a, Either (f a) (g a)
               , eitherF Left Right, either InL InR )

HasTrieIsomorph( HasTrie (g (f a))
               , (g :. f) a, g (f a) , unO, O )


-- newtype ListTrie a v = ListTrie (PF [a] [a] :-> v)
-- instance HasTrie a => HasTrie [a] where
--   type STrie [a] = ListTrie a
--   sTrie f = ListTrie (trie (f . wrap))
--   sUntrie (ListTrie t) = sUntrie t . unwrap
--   enumerate (ListTrie t) = (result.fmap.first) wrap enumerate $ t
-- HasTrieIsomorph( HasTrie (PF ([a]) ([a]) :->: v)
--                , ListTrie a v, PF ([a]) ([a]) :->: v
--                , \ (ListTrie w) -> w, ListTrie )


-- Works.  Now abstract into a macro

#define HasTrieRegular(Context,Type,TrieType,TrieCon) \
newtype TrieType v = TrieCon (PF (Type) (Type) :->: v); \
instance Context => HasTrie (Type) where { \
  type STrie (Type) = TrieType; \
  sTrie f = TrieCon (sTrie (f . wrap)); \
  sUntrie (TrieCon t) = sUntrie t . unwrap; \
  enumerate (TrieCon t) = (result.fmap.first) wrap enumerate t; \
}; \
HasTrieIsomorph( HasTrie (PF (Type) (Type) :->: v) \
               , TrieType v, PF (Type) (Type) :->: v \
               , \ (TrieCon w) -> w, TrieCon )

-- For instance,

-- HasTrieRegular(HasTrie a, [a]   , ListTrie a, ListTrie)
-- HasTrieRegular(HasTrie a, Tree a, TreeTrie a, TreeTrie)

-- Simplify a bit with a macro for unary regular types.
-- Make similar defs for binary etc as needed.

#define HasTrieRegular1(TypeCon,TrieCon) \
HasTrieRegular(HasTrie a, TypeCon a, TrieCon a, TrieCon)

HasTrieRegular1([]  , ListTrie)
HasTrieRegular1(Tree, TreeTrie)


-- HasTrieIsomorph(Context,Type,IsoType,toIso,fromIso)

-- HasTrieIsomorph( HasTrie (PF [a] [a] :->: v)
--                , ListTrie a v, PF [a] [a] :->: v
--                , \ (ListTrie w) -> w, ListTrie )


enumerateEnum :: (Enum k, Num k, HasTrie k) => (k :->: v) -> [(k,v)]
enumerateEnum t = [(k, f k) | k <- [0 ..] `weave` [-1, -2 ..]]
 where
   f = untrie t

#define HasTrieIntegral(Type) \
instance HasTrie Type where { \
  type STrie Type = IT.IntTrie; \
  sTrie   = (<$> IT.identity); \
  sUntrie = IT.apply; \
  enumerate = enumerateEnum; \
}

HasTrieIntegral(Int)
HasTrieIntegral(Integer)


-- Memoizing higher-order functions

HasTrieIsomorph((HasTrie a, HasTrie (a :->: b)), a -> b, a :->: b, trie, untrie)


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

ft1 :: (Bool -> a) -> [a]
ft1 f = [f False, f True]

f1 :: Bool -> Int
f1 False = 0
f1 True  = 1

trie1a :: HasTrie a => (Bool -> a) :->: [a]
trie1a = trie ft1

trie1b :: HasTrie a => (Bool :->: a) :->: [a]
trie1b = trie1a

trie1c :: HasTrie a => (Either () () :->: a) :->: [a]
trie1c = trie1a

trie1d :: HasTrie a => ((Trie () :*: Trie ()) a) :->: [a]
trie1d = trie1a

trie1e :: HasTrie a => (Trie () a, Trie () a) :->: [a]
trie1e = trie1a

trie1f :: HasTrie a => (() :->: a, () :->: a) :->: [a]
trie1f = trie1a

trie1g :: HasTrie a => (a, a) :->: [a]
trie1g = trie1a

trie1h :: HasTrie a => (Trie a :. Trie a) [a]
trie1h = trie1a

trie1i :: HasTrie a => a :->: a :->: [a]
trie1i = unO trie1a


ft2 :: ([Bool] -> Int) -> Int
ft2 f = f (alts 15)

alts :: Int -> [Bool]
alts n = take n (cycle [True,False])

f2 :: [Bool] -> Int
f2 = length . filter id

-- Memoization fails:

-- *FunctorCombo.MemoTrie> ft2 f2
-- 8
-- *FunctorCombo.MemoTrie> memo ft2 f2
-- ... (hang forever) ...

-- Would nonstrict memoization work?  <http://conal.net/blog/posts/nonstrict-memoization/>

f3 :: Bool -> Integer
f3 = const 3

-- *FunctorCombo.MemoTrie> f3 undefined
-- 3
-- *FunctorCombo.MemoTrie> memo f3 undefined
-- *** Exception: Prelude.undefined

f4 :: () -> Integer
f4 = const 4

-- *FunctorCombo.MemoTrie> f4 undefined
-- 4
-- *FunctorCombo.MemoTrie> memo f4 undefined
-- 4

f5 :: ((),()) -> Integer
f5 = const 5

-- *FunctorCombo.MemoTrie> f5 undefined
-- 5
-- *FunctorCombo.MemoTrie> memo f5 undefined
-- 5

f6 :: Either () () -> Integer
f6 = const 6

-- *FunctorCombo.MemoTrie> f6 undefined
-- 6
-- *FunctorCombo.MemoTrie> memo f6 undefined
-- *** Exception: Prelude.undefined

-- Aha!

t6 :: Either () () :-> Integer
t6 = trie f6

-- *FunctorCombo.MemoTrie> t6
-- Id 6 :*: Id 6

-}
