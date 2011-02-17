{-# LANGUAGE TypeOperators, TypeFamilies, UndecidableInstances, CPP
           , DeriveFunctor, StandaloneDeriving
           , FlexibleContexts
 #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-unused-imports #-}  -- TEMP
----------------------------------------------------------------------
-- |
-- Module      :  FunctorCombo.NonstrictMemo
-- Copyright   :  (c) Conal Elliott 2010
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Functor-based memo tries.  See
-- <http://conal.net/blog/posts/details-for-nonstrict-memoization-part-1/>
----------------------------------------------------------------------

module FunctorCombo.NonstrictMemo
  (
    HasTrie(..),(:->:),memo,memo2,memo3
  ) where

#define NonstrictMemo

import Control.Arrow (first)
import Control.Applicative ((<$>))

import qualified Data.IntTrie as IT  -- data-inttrie
import Data.Tree

import Control.Compose (result)  -- TypeCompose

#ifdef NonstrictMemo
import Data.Lub
#endif

import FunctorCombo.Strict
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

#define FunctorSuperClass

#ifdef FunctorSuperClass

#define HasTrieContext(Ty) Functor (STrie (Ty))
#define HF(Ty) HasTrie (Ty)

#else
#define HasTrieContext(Ty) ()
#define HF(Ty) HasTrie (Ty), Functor (STrie (Ty))

#endif


#ifdef NonstrictMemo
data Trie k v = Trie v (STrie k v)

deriving instance Functor (STrie k) => Functor (Trie k)

-- instance Functor (STrie k) => Functor (Trie k) where
--   fmap f (Trie b t) = Trie (f b) (fmap f t)

type k :->: v = Trie k v

-- Bottom
bottom :: a
bottom = error "MemoTrie: evaluated bottom.  Oops!"

-- | Create the trie for the entire domain of a function
trie   :: (HasTrie k{-, HasLub v-}) => (k  ->  v) -> (k :->: v)
trie f = Trie (f bottom) (sTrie f)

-- | Convert k trie to k function, i.e., access k field of the trie
untrie :: (HasTrie k, HasLub v) => (k :->: v) -> (k  ->  v)
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

-- | Strict memo trie from k to v
type k :-> v = STrie k v

-- | Domain types with associated memo tries
class HasTrieContext(k) => HasTrie k where
    -- | Representation of trie with domain type @a@
    type STrie k :: * -> *
    -- | Create the trie for the entire domain of a function
    sTrie   :: {- HasLub(v) => -} (k  -> v) -> (k :-> v)
    -- | Convert k trie to k function, i.e., access k field of the trie
    sUntrie :: HasLub(v) => (k :-> v) -> (k  -> v)

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
  sUntrie (Id v) = \ () -> v
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

instance (HF(a), HasTrie b) => HasTrie (a , b) where
  type STrie (a , b) = Trie a :. Trie b
--   sTrie   f = O (trie (trie . curry f))
--   sUntrie (O tt) = uncurry (untrie . untrie tt)
  sTrie   f = O (fmap trie (trie (curry f)))
  sUntrie (O tt) = uncurry (untrie (fmap untrie tt))

--   enumerate (O tt) =
--     [ ((a,b),x) | (a,t) <- enumerate tt , (b,x) <- enumerate t ]

-- With the first definitions of sTrie and sUntrie:
-- 
--     Could not deduce (HasLub (Trie b v)) from the context (HasLub v)
--       arising from a use of `trie'
-- 
--     Could not deduce (HasLub (Trie b v)) from the context (HasLub v)
--       arising from a use of `untrie'
-- 
-- Solution: switch from inner-then-outer to outer-then-inner.


-- Experiment: strict sums & pairs.
-- TODO: re-work non-strict versions in terms of strict ones and Lift

instance (HasTrie a, HasTrie b) => HasTrie (a :+! b) where
  type STrie (a :+! b) = STrie a :*: STrie b
  sTrie   f           = sTrie (f . Left') :*: sTrie (f . Right')
  sUntrie (ta :*: tb) = sUntrie ta `either'` sUntrie tb
--   enumerate (ta :*: tb) = enum' Left' ta `weave` enum' Right' tb

instance (HF(a), HasTrie b) => HasTrie (a :*! b) where
  type STrie (a :*! b) = STrie a :. STrie b
--   sTrie   f = O (trie (trie . curry f))
--   sUntrie (O tt) = uncurry (untrie . untrie tt)
  sTrie   f      = O (fmap sTrie (sTrie (curry' f)))
  sUntrie (O tt) = uncurry' (sUntrie (fmap sUntrie tt))

-- Lift a has an additional bottom.  A strict function or trie is
-- only strict in the lower (outer) one.
instance (HF(a)) => HasTrie (Lift a) where
  type STrie (Lift a) = Trie a
  sTrie   f = trie (f . Lift)
  sUntrie t = untrie t . unLift


#define HasTrieIsomorph(Context,Type,IsoType,toIso,fromIso) \
instance Context => HasTrie (Type) where { \
  type STrie (Type) = STrie (IsoType); \
  sTrie f = sTrie (f . (fromIso)); \
  sUntrie t = sUntrie t . (toIso); \
}

  -- enumerate = (result.fmap.first) (fromIso) enumerate; \


HasTrieIsomorph( (), Bool, Either () ()
               , bool (Left ()) (Right ())
               , either (\ () -> True) (\ () -> False))

HasTrieIsomorph( (HF(a),HF(b), HasTrie c)
               , (a,b,c), ((a,b),c)
               , \ (a,b,c) -> ((a,b),c), \ ((a,b),c) -> (a,b,c))

HasTrieIsomorph( (HF(a),HF(b),HF(c), HasTrie d)
               , (a,b,c,d), ((a,b,c),d)
               , \ (a,b,c,d) -> ((a,b,c),d), \ ((a,b,c),d) -> (a,b,c,d))

-- OOPS! Fix the isomorphs above


-- As well as the functor combinators themselves

HasTrieIsomorph( HasTrie x, Const x a, x, getConst, Const )

HasTrieIsomorph( HasTrie a, Id a, a, unId, Id )

HasTrieIsomorph( ( HF(f a), HasTrie (g a) )
               , (f :*: g) a, (f a,g a)
               , \ (fa :*: ga) -> (fa,ga), \ (fa,ga) -> (fa :*: ga) )

HasTrieIsomorph( (HasTrie (f a), HasTrie (g a))
               , (f :+: g) a, Either (f a) (g a)
               , eitherF Left Right, either InL InR )

HasTrieIsomorph( HasTrie (g (f a))
               , (g :. f) a, g (f a) , unO, O )

-- Strict variants

HasTrieIsomorph( ( HF(f a), HasTrie (g a) )
               , (f :*:! g) a, (f a :*! g a)
               , \ (fa :*:! ga) -> (fa :*! ga), \ (fa :*! ga) -> (fa :*:! ga) )

HasTrieIsomorph( (HasTrie (f a), HasTrie (g a))
               , (f :+:! g) a, (f a :+! g a)
               , fToSum, sumToF)

-- Factored out to avoid clash between primes and GHC's use of classic CPP
sumToF :: (f a :+! g a) -> (f :+:! g) a
sumToF = either' InL' InR'

fToSum :: (f :+:! g) a -> (f a :+! g a)
fToSum = eitherF' Left' Right'

newtype ListSTrie a v = ListSTrie (PF [a] [a] :-> v)
 
deriving instance Functor (STrie a) => Functor (ListSTrie a)
 
instance (HF(a)) => HasTrie [a] where
  type STrie [a] = ListSTrie a
  sTrie f = ListSTrie (sTrie (f . wrap))
  sUntrie (ListSTrie t) = sUntrie t . unwrap
  -- enumerate (ListSTrie t) = (result.fmap.first) wrap enumerate $ t

-- Compiles fine, but has many points of undefinedness than a list does.  See
-- <http://conal.net/blog/posts/details-for-nonstrict-memoization-part-1/>
-- 
-- Experiment with some alternatives.


-- Now a trie for ListSTrie a v.  Use the isomorphism with PF [a] [a] :-> v

-- HasTrieIsomorph( HasTrie (PF ([a]) ([a]) :->: v)
--                , ListSTrie a v, PF ([a]) ([a]) :->: v
--                , \ (ListSTrie w) -> w, ListSTrie )


-- instance HasTrie (PF ([a]) ([a]) :->: v) => HasTrie (ListSTrie a v) where
--   type STrie (ListSTrie a v) = STrie (PF ([a]) ([a]) :->: v)
--   sTrie f = sTrie (f . ListSTrie)
--   -- sUntrie t = sUntrie t . (\ (ListSTrie w) -> w)


--     Could not deduce (HasTrie (Trie ((:*:) (Const a) Id [a]) v),
--                       Functor (STrie (Trie (Const () [a]) v)),
--                       HasTrie (Trie (Const () [a]) v))
--       from the context (HasLub v1)
--       arising from a use of `sTrie'

--     Couldn't match expected type `STrie
--                                     (Trie ((:+:) Unit (Const a :*: Id) [a]) v)'
--            against inferred type `Trie (Trie (Const () [a]) v)
--                                   :. Trie (Trie ((:*:) (Const a) Id [a]) v)'
--       NB: `STrie' is a type function, and may not be injective
--     In the expression: sTrie (f . ListSTrie)

{-

f :: ListSTrie a v -> u

ListSTrie :: (PF [a] [a] :-> v) -> ListSTrie a v

f . ListSTrie :: (PF [a] [a] :-> v) -> u

sTrie (f . ListSTrie) :: HasTrie (PF [a] [a] :-> v) => (PF [a] [a] :-> v) :-> u
                     :: HasTrie (PF [a] [a] :-> v) => ListSTrie a v :-> u

ListSTrie a v :-> u

(PF [a] [a] :-> v) :-> u

((Unit :+: Const a :*: Id) [a] :-> v) :-> u

(Either (Unit [a]) ((Const a :*: Id) [a]) :-> v) :-> u

STrie (Either (Unit [a]) ((Const a :*: Id) [a])) v :-> u

(Trie (Unit [a]) :*: Trie ((Const a :*: Id) [a])) v :-> u

(Trie (Unit [a]) v , Trie ((Const a :*: Id) [a]) v) :-> u

(Unit [a] :->: v , (Const a :*: Id) [a] :->: v) :-> u

STrie (Unit [a] :->: v , (Const a :*: Id) [a] :->: v) u

(Trie (Unit [a] :->: v) :. Trie ((Const a :*: Id) [a] :->: v)) u

(Trie (Unit [a] :->: v) :. Trie ((Const a [a], Id [a]) :->: v)) u

(Trie (Unit [a] :->: v) :. Trie ((Const a [a], Id [a]) :->: v)) u


(v , (Const a [a], Id [a]) :-> v)

(v , Const a [a] :->: Id [a] :->: v)

(v , (Id [a] :->: v, Const a [a] :-> Id [a] :->: v))

(v , (Id [a] :->: v, Const a [a] :-> (v, Id [a] :-> v)))

(v , ((v, Id [a] :-> v), Const a [a] :-> (v, Id [a] :-> v)))

(v , ((v, [a] :->: v), a :->: (v, [a] :->: v)))



ListSTrie a v

PF [a] [a] :-> v

(Unit :+: Const a :*: Id) [a] :-> v

Either (Unit [a]) ((Const a :*: Id) [a]) :-> v

STrie (Either (Unit [a]) ((Const a :*: Id) [a])) v

(Trie (Unit [a]) :*: Trie ((Const a :*: Id) [a])) v


-}

-- Now abstract into a macro

#define HasTrieRegular(Context,Type,TrieType,TrieCon) \
newtype TrieType v = TrieCon (PF (Type) (Type) :->: v); \
instance Context => HasTrie (Type) where { \
  type STrie (Type) = TrieType; \
  sTrie f = TrieCon (sTrie (f . wrap)); \
  sUntrie (TrieCon t) = sUntrie t . unwrap; \
}; \
HasTrieIsomorph( HasTrie (PF (Type) (Type) :->: v) \
               , TrieType v, PF (Type) (Type) :->: v \
               , \ (TrieCon w) -> w, TrieCon )

--   enumerate (TrieCon t) = (result.fmap.first) wrap enumerate t; \



-- For instance,

-- HasTrieRegular(HasTrie a, [a]   , ListSTrie a, ListSTrie)
-- HasTrieRegular(HasTrie a, Tree a, TreeTrie a, TreeTrie)

-- Simplify a bit with a macro for unary regular types.
-- Make similar defs for binary etc as needed.

#define HasTrieRegular1(TypeCon,TrieCon) \
HasTrieRegular(HasTrie a, TypeCon a, TrieCon a, TrieCon)

-- HasTrieRegular1([]  , ListSTrie)
-- HasTrieRegular1(Tree, TreeTrie)


-- HasTrieIsomorph(Context,Type,IsoType,toIso,fromIso)

-- HasTrieIsomorph( HasTrie (PF [a] [a] :->: v)
--                , ListSTrie a v, PF [a] [a] :->: v
--                , \ (ListSTrie w) -> w, ListSTrie )


-- enumerateEnum :: (Enum k, Num k, HasTrie k) => (k :->: v) -> [(k,v)]
-- enumerateEnum t = [(k, f k) | k <- [0 ..] `weave` [-1, -2 ..]]
--  where
--    f = untrie t

#define HasTrieIntegral(Type) \
instance HasTrie Type where { \
  type STrie Type = IT.IntTrie; \
  sTrie   = (<$> IT.identity); \
  sUntrie = IT.apply; \
}
  -- enumerate = enumerateEnum;

HasTrieIntegral(Int)
HasTrieIntegral(Integer)

-- Memoizing higher-order functions

HasTrieIsomorph((HasTrie a, HasTrie (a :->: b), HasLub b)
               ,a -> b, a :->: b, trie, untrie)


{--------------------------------------------------------------------
    Regular instances.
--------------------------------------------------------------------}

-- Re-think where to put these instances.  I want different versions for
-- list, depending on whether I'm taking care with bottoms.

instance Regular [a] where
  type PF [a] = Unit :+:! Const (Lift a) :*:! Lift
  unwrap []     = InL' (Const ())
  unwrap (a:as) = InR' (Const (Lift a) :*:! Lift as)
  wrap (InL' (Const ()))            = []
  wrap (InR' (Const (Lift a) :*:! Lift as)) = a:as

-- Rose tree (from Data.Tree)
-- 
--   data Tree  a = Node a [Tree a]

-- instance Functor Tree where
--   fmap f (Node a ts) = Node (f a) (fmap f ts)

instance Regular (Tree a) where
  type PF (Tree a) = Const a :*: []
  unwrap (Node a ts) = Const a :*: ts
  wrap (Const a :*: ts) = Node a ts

-- Note that we're using the non-strict pairing functor.
-- Does PF (Tree a) have the right strictness?
-- I think so, since a tree can be either _|_ or Node applied to a
-- possibly-_|_ value and a possibly-_|_ list.

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

{-

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
