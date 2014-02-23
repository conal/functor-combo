{-# LANGUAGE TypeOperators, TypeFamilies, UndecidableInstances, CPP
           , FlexibleContexts, DeriveFunctor, StandaloneDeriving
           , GADTs
 #-}

{-# OPTIONS_GHC -Wall -fno-warn-orphans  #-}
{-# OPTIONS_GHC -fno-warn-unused-binds   #-}  -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-}  -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  FunctorCombo.StrictMemo
-- Copyright   :  (c) Conal Elliott 2010-2012
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Functor-based memo tries (strict for now)
-- 
----------------------------------------------------------------------

module FunctorCombo.StrictMemo
  (
    HasTrie(..),(:->:),(!),memo,memo2,memo3,idTrie
  , onUntrie, onUntrie2
  , TrieTree(..)
  ) where

import Data.Functor ((<$>))
import Data.Foldable (Foldable(..),toList)
import Data.Traversable (Traversable(..))
import Control.Applicative (Applicative(..),liftA2)
-- import Control.Arrow (first)

-- import Data.Tree

import qualified Data.IntTrie as IT  -- data-inttrie
import Data.Tree

-- import Control.Compose (result,(<~))  -- TypeCompose

import TypeUnary.Vec (Z,S,Vec(..),IsNat(..),Nat(..))

-- import FunctorCombo.Strict
import FunctorCombo.Functor
import FunctorCombo.Pair
import FunctorCombo.Regular


{--------------------------------------------------------------------
    Class
--------------------------------------------------------------------}

infixr 0 :->:

-- | Memo trie from k to v
type k :->: v = Trie k v


#define FunctorSuperClass

#ifdef FunctorSuperClass

#define HasTrieContext(Ty) Functor (Trie(Ty))
#define HF(Ty) HasTrie (Ty)

#else
#define HasTrieContext(Ty) ()
#define HF(Ty) HasTrie (Ty), Functor (Trie (Ty))

#endif

-- | Domain types with associated memo tries
class HasTrieContext(k) => HasTrie k where
    -- | Representation of trie with domain type @a@
    type Trie k :: * -> *
    -- | Create the trie for the entire domain of a function
    trie   :: (k  ->  v) -> (k :->: v)
    -- | Convert k trie to k function, i.e., access k field of the trie
    untrie :: (k :->: v) -> (k  ->  v)
--     -- | List the trie elements.  Order of keys (@:: k@) is always the same.
--     enumerate :: (k :->: v) -> [(k,v)]

-- | Indexing. Synonym for 'untrie'.
(!) :: HasTrie k => (k :->: v) -> k  ->  v
(!) = untrie

-- -- | Domain elements of a trie
-- domain :: HasTrie a => [a]
-- domain = map fst (enumerate (trie (const oops)))
--  where
--    oops = error "Data.MemoTrie.domain: range element evaluated."

-- Identity trie. To do: make idTrie the method, and define trie via idTrie.
idTrie :: HasTrie k => k :->: k
idTrie = trie id

-- | List the trie elements.  Order of keys (@:: k@) is always the same.
enumerate :: (Foldable (Trie k), HasTrie k) => (k :->: v) -> [(k,v)]
enumerate = zip (toList idTrie) . toList

-- TODO: Improve this implementation, using an interface from Edward
-- Kmett. Something about collections with keys, so that I can efficiently
-- implement `(k :->: v) -> (k :->: (k,v))`.


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
  untrie (Id v) = \ () -> v
--   enumerate (Id a) = [((),a)]

instance (HasTrie a, HasTrie b) => HasTrie (Either a b) where
  type Trie (Either a b) = Trie a :*: Trie b
  trie   f           = trie (f . Left) :*: trie (f . Right)
  untrie (ta :*: tb) = untrie ta `either` untrie tb
--   enumerate (ta :*: tb) = enum' Left ta `weave` enum' Right tb

-- enum' :: (HasTrie a) => (a -> a') -> (a :->: b) -> [(a', b)]
-- enum' f = (fmap.first) f . enumerate

weave :: [a] -> [a] -> [a]
[] `weave` as = as
as `weave` [] = as
(a:as) `weave` bs = a : (bs `weave` as)

instance (HF(a), HasTrie b) => HasTrie (a , b) where
  type Trie (a , b) = Trie a :. Trie b
  trie   f = O (trie (trie . curry f))
  -- untrie (O tt) = uncurry (untrie . untrie tt)
  untrie (O tt) = uncurry (untrie (fmap untrie tt))
  -- With the first form of untrie, I only need HasTrie a, not also
  -- Functor (Trie a) in the case of FunctorSuperClass
--   enumerate (O tt) =
--     [ ((a,b),x) | (a,t) <- enumerate tt , (b,x) <- enumerate t ]



#define HasTrieIsomorph(Context,Type,IsoType,toIso,fromIso) \
instance Context => HasTrie (Type) where {\
  type Trie (Type) = Trie (IsoType); \
  trie f = trie (f . (fromIso)); \
  untrie t = untrie t . (toIso); \
}

--  enumerate = (result.fmap.first) (fromIso) enumerate;

-- HasTrieIsomorph( (), Bool, Either () ()
--                , bool (Right ()) (Left ())
--                , either (\ () -> False) (\ () -> True))

instance HasTrie Bool where
  type Trie Bool = Pair
  trie f = (f False :# f True)
  untrie (f :# t) c = if c then t else f

HasTrieIsomorph( (HF(a),HF(b), HasTrie c)
               , (a,b,c), ((a,b),c)
               , \ (a,b,c) -> ((a,b),c), \ ((a,b),c) -> (a,b,c))

HasTrieIsomorph( (HF(a),HF(b),HF(c), HasTrie d)
               , (a,b,c,d), ((a,b,c),d)
               , \ (a,b,c,d) -> ((a,b,c),d), \ ((a,b,c),d) -> (a,b,c,d))



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



-- newtype ListTrie a v = ListTrie (PF [a] [a] :->: v)
 
-- instance (HF(a)) => HasTrie [a] where
--   type Trie [a] = ListTrie a
--   trie f = ListTrie (trie (f . wrap))
--   untrie (ListTrie t) = untrie t . unwrap
--   enumerate (ListTrie t) = (result.fmap.first) wrap enumerate $ t
 
-- deriving instance Functor (Trie a) => Functor (ListTrie a)
 
-- HasTrieIsomorph( HasTrie (PF ([a]) ([a]) :->: v)
--                , ListTrie a v, PF ([a]) ([a]) :->: v
--                , \ (ListTrie w) -> w, ListTrie )

-- instance HasTrie (PF ([a]) ([a]) :->: v) => HasTrie (ListTrie a v) where
--   type Trie (ListTrie a v) = Trie (PF ([a]) ([a]) :->: v)
--   trie f = trie (f . ListTrie)
--   untrie t = untrie t . \ (ListTrie w) -> w

-- instance (HasTrie (PF ([a]) ([a]) :->: v)) => HasTrie (ListTrie a v) where
--   type Trie (ListTrie a v) = Trie (PF ([a]) ([a]) :->: v)

-- instance (Functor (Trie v), HasTrie (PF ([a]) ([a]) :->: v)) => HasTrie (ListTrie a v) where
--   type Trie (ListTrie a v) = Trie (PF ([a]) ([a]) :->: v)

--     Could not deduce (Functor
--                         (Trie (Trie (Const a [a]) (ListTrie a v))))
--       from the context (Functor (Trie v), HasTrie (PF [a] [a] :->: v))
--       arising from the superclasses of an instance declaration

--     Functor (Trie (Trie (Const a [a]) (ListTrie a v)))

--     Functor (Trie (Const a [a] :->: ListTrie a v))

--     Const a [a] :->: ListTrie a v

--     a :->: ListTrie a v

-- instance (Functor (Trie a), Functor (Trie v), HasTrie (PF ([a]) ([a]) :->: v)) => HasTrie (ListTrie a v) where
--   type Trie (ListTrie a v) = Trie (PF ([a]) ([a]) :->: v)

--     Could not deduce (Functor (Trie (Trie a (ListTrie a v)))) ...
--       arising from the superclasses of an instance declaration


-- newtype ListTrie a v = ListTrie (PF [a] [a] :->: v)
 
-- instance HasTrie a => HasTrie [a] where
--   type Trie [a] = ListTrie a
--   trie f = ListTrie (trie (f . wrap))
--   untrie (ListTrie t) = untrie t . unwrap
--   enumerate (ListTrie t) = (result.fmap.first) wrap enumerate $ t
 
-- HasTrieIsomorph( HasTrie (PF ([a]) ([a]) :->: v)
--                , ListTrie a v, PF ([a]) ([a]) :->: v
--                , \ (ListTrie w) -> w, ListTrie )
 
-- deriving instance Functor (Trie a) => Functor (ListTrie a)


-- newtype ListTrie a v = ListTrie (PF ([a]) ([a]) :->: v); \
-- instance HasTrie a => HasTrie ([a]) where { \
--   type Trie ([a]) = ListTrie a; \
--   trie f = ListTrie (trie (f . wrap)); \
--   untrie (ListTrie t) = untrie t . unwrap; \
--   enumerate (ListTrie t) = (result.fmap.first) wrap enumerate t; \
-- }; \
-- HasTrieIsomorph( HasTrie (PF ([a]) ([a]) :->: v) \
--                , ListTrie a v, PF ([a]) ([a]) :->: v \
--                , \ (ListTrie w) -> w, ListTrie )
 
-- deriving instance Functor (Trie a) => Functor (ListTrie a)

-- Works.  Now abstract into a macro

#define HasTrieRegular(Context,Type,TrieType,TrieCon) \
newtype TrieType v = TrieCon (PF (Type) (Type) :->: v); \
instance Context => HasTrie (Type) where { \
  type Trie (Type) = TrieType; \
  trie f = TrieCon (trie (f . wrap)); \
  untrie (TrieCon t) = untrie t . unwrap; \
}; \
HasTrieIsomorph( HasTrie (PF (Type) (Type) :->: v) \
               , TrieType v, PF (Type) (Type) :->: v \
               , \ (TrieCon w) -> w, TrieCon )

--  enumerate (TrieCon t) = (result.fmap.first) wrap enumerate t; 


-- For instance,

-- HasTrieRegular(HasTrie a, [a] , ListTrie a, ListTrie)
-- -- deriving instance Functor (Trie a) => Functor (ListTrie a)
 
-- HasTrieRegular(HasTrie a, Tree a, TreeTrie a, TreeTrie)
-- -- deriving instance Functor (Trie a) => Functor (TreeTrie a)

-- Simplify a bit with a macro for unary regular types.
-- Make similar defs for binary etc as needed.

#define HasTrieRegular1(TypeCon,TrieCon) \
HasTrieRegular((HF(a)), TypeCon a, TrieCon a, TrieCon); \
deriving instance Functor (Trie a) => Functor (TrieCon a)

HasTrieRegular1([]  , ListTrie)
HasTrieRegular1(Tree, TreeTrie)

-- HasTrieIsomorph(Context,Type,IsoType,toIso,fromIso)

-- HasTrieIsomorph( HasTrie (PF [a] [a] :->: v)
--                , ListTrie a v, PF [a] [a] :->: v
--                , \ (ListTrie w) -> w, ListTrie )





-- enumerateEnum :: (Enum k, Num k, HasTrie k) => (k :->: v) -> [(k,v)]
-- enumerateEnum t = [(k, f k) | k <- [0 ..] `weave` [-1, -2 ..]]
--  where
--    f = untrie t

#define HasTrieIntegral(Type) \
instance HasTrie Type where { \
  type Trie Type = IT.IntTrie; \
  trie   = (<$> IT.identity); \
  untrie = IT.apply; \
}

--  enumerate = enumerateEnum;


HasTrieIntegral(Int)
HasTrieIntegral(Integer)


-- Memoizing higher-order functions

HasTrieIsomorph((HasTrie a, HasTrie (a :->: b)), a -> b, a :->: b, trie, untrie)

-- -- Convenience Pair functor
-- instance HasTrie a => HasTrie (Pair a) where
--   type Trie (Pair a) = Trie a :. Trie a
--   trie f = O (trie (\ a -> trie (\ b -> f (a :# b))))
--   untrie (O tt) (a :# b) = untrie (untrie tt a) b

HasTrieIsomorph((HF(a))
               , Pair a, (a,a)
               , \ (a :# a') -> (a,a'), \ (a,a') -> (a :# a'))

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

type Unop a = a -> a

bool :: a -> a -> Bool -> a
bool t e b = if b then t else e


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



ft1 :: (Bool -> a) -> [a]
ft1 f = [f False, f True]

f1 :: Bool -> Int
f1 False = 0
f1 True  = 1

trie1a :: (HF(a)) => (Bool -> a) :->: [a]
trie1a = trie ft1

trie1b :: (HF(a)) => (Bool :->: a) :->: [a]
trie1b = trie1a

trie1c :: (HF(a)) => (Either () () :->: a) :->: [a]
trie1c = trie1a

trie1d :: (HF(a)) => ((Trie () :*: Trie ()) a) :->: [a]
trie1d = trie1a

trie1e :: (HF(a)) => (Trie () a, Trie () a) :->: [a]
trie1e = trie1a

trie1f :: (HF(a)) => (() :->: a, () :->: a) :->: [a]
trie1f = trie1a

trie1g :: (HF(a)) => (a, a) :->: [a]
trie1g = trie1a

trie1h :: (HF(a)) => (Trie a :. Trie a) [a]
trie1h = trie1a

trie1i :: (HF(a)) => a :->: a :->: [a]
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

{--------------------------------------------------------------------
    Regular instances.
--------------------------------------------------------------------}

-- Re-think where to put these instances.  I want different versions for
-- list, depending on whether I'm taking care with bottoms.

instance Regular [a] where
  type PF [a] = Unit :+: Const a :*: Id
  unwrap []     = InL (Const ())
  unwrap (a:as) = InR (Const a :*: Id as)
  wrap (InL (Const ()))          = []
  wrap (InR (Const a :*: Id as)) = a:as

-- Rose tree (from Data.Tree)
-- 
--   data Tree  a = Node a [Tree a]

-- instance Functor Tree where
--   fmap f (Node a ts) = Node (f a) (fmap f ts)

instance Regular (Tree a) where
  type PF (Tree a) = Const a :*: []
  unwrap (Node a ts) = Const a :*: ts
  wrap (Const a :*: ts) = Node a ts

{--------------------------------------------------------------------
    Acting on function
--------------------------------------------------------------------}

onUntrie :: (HasTrie a, HasTrie b) =>
            ((a  ->  a') -> (b  ->  b'))
         -> ((a :->: a') -> (b :->: b'))
onUntrie = trie <~ untrie

onUntrie2  :: (HasTrie a, HasTrie b, HasTrie c) =>
             ((a  ->  a') -> (b  ->  b') -> (c  ->  c'))
          -> ((a :->: a') -> (b :->: b') -> (c :->: c'))
onUntrie2 = onUntrie <~ untrie

{--------------------------------------------------------------------
    Vector tries
--------------------------------------------------------------------}

data TrieTree :: * -> * -> * -> * where
  L :: a -> TrieTree Z k a
  B :: (k :->: TrieTree n k a) -> TrieTree (S n) k a

-- deriving instance Show a => Show (TrieTree n k a)

-- instance Show a => Show (T n a) where
--   showsPrec p (L a)  = showsApp1 "L" p a
--   showsPrec p (B uv) = showsApp1 "B" p uv


instance Functor (Trie k) => Functor (TrieTree n k) where
  fmap f (L a ) = L (f a)
  fmap f (B ts) = B ((fmap.fmap) f ts)

instance (Applicative (Trie k), IsNat n) => Applicative (TrieTree n k) where
  pure = pureV nat
  (<*>) = apV nat

apV :: Applicative (Trie k) => Nat n -> TrieTree n k (a -> b) -> TrieTree n k a -> TrieTree n k b
apV Zero     (L f ) (L x ) = L (f x)
apV (Succ n) (B fs) (B xs) = B (liftA2 (apV n) fs xs)
apV _ _ _ = error "apV: Impossible, but GHC doesn't know it"

-- joinV :: TrieTree n k (TrieTree n k a) -> TrieTree n k a
-- joinV = ...

-- TODO: Maybe redo these instances via the semantic instances.
-- Define instance templates in StrictMemo.

pureV :: Applicative (Trie k) => Nat n -> a -> TrieTree n k a
pureV Zero     = L
pureV (Succ n) = B . pure . pureV n

instance Foldable (Trie k) => Foldable (TrieTree n k) where
  foldMap f (L a)  = f a
  foldMap f (B ts) = (foldMap.foldMap) f ts

instance (Functor (Trie k), Foldable (Trie k), Traversable (Trie k)) =>
         Traversable (TrieTree n k) where
  traverse f (L a)  = L <$> f a
  traverse f (B ts) = B <$> (traverse.traverse) f ts

instance (HasTrie k, Functor (Trie k), IsNat n) => HasTrie (Vec n k) where
  type Trie (Vec n k) = TrieTree n k
  untrie = untrieV nat
  trie   = trieV   nat

untrieV :: (HasTrie k) =>
           Nat n -> (Vec n k :->: v) -> (Vec n k -> v)
untrieV Zero     (L a ) ZVec      = a
untrieV (Succ n) (B ts) (k :< ks) = untrieV n (untrie ts k) ks
untrieV _ _ _ = error "untrieV: Impossible, but GHC doesn't know it"

trieV :: HasTrie k =>
         Nat n -> (Vec n k -> v) -> (Vec n k :->: v)
trieV Zero     f = L (f ZVec)
trieV (Succ _) f = B (unO (trie (f . uncurry (:<))))

-- f :: Vec (S n) k -> v
-- f . uncurry (:<) :: k :* Vec n k -> v
-- trie (f . uncurry (:<)) :: k :* Vec n k :->: v
--                         :: (Trie k :. Trie (Vec n k)) v
--                         :: (Trie k :. TrieTree n k) v
-- unO (trie (f . uncurry (:<))) :: k :->: TrieTree n k v
-- B (unO (trie (f . uncurry (:<)))) :: TrieTree (S n) k v
--                                   :: Vec (S n) k :->: v
