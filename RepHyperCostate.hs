{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
module RepresentableHyperfunctions where

import Control.Arrow
import Control.Category
import Control.Monad.Fix
import Data.Coerce
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Rep
import Data.Profunctor
import Data.Profunctor.Unsafe
import Data.Distributive
import Prelude hiding ((.),id)

-- | Hyperfunctions as an explicit "nu" form, but using a representable functor
-- to describe the "state space" of the hyperfunction. This permits memoization
-- but doesn't require it.
--
-- 'arr' is a faithful functor, so
--
-- @'arr' f ≡ 'arr' g@ implies @f ≡ g@
--

data Hyper a b where
  Hyper :: Representable g => (g a -> g b) -> Rep g -> Hyper a b

instance Category Hyper where
  id = Hyper (id :: forall a. Identity a -> Identity a) ()
  Hyper f x . Hyper g y = Hyper (Compose . collect f . collect g . getCompose) (x,y)

instance Arrow Hyper where
  arr f = Hyper (Identity #. f .# runIdentity) ()

  first (Hyper f x) = Hyper f' x where
    f' fac = tabulate $ \i -> (index fb i, snd (index fac i)) where fb = f (fmap fst fac)

  second (Hyper f x) = Hyper f' x where
    f' fca = tabulate $ \i -> (fst (index fca i), index fb i) where fb = f (fmap snd fca)

  Hyper (f :: f a -> f b) x *** Hyper (g :: g c -> g d) y = Hyper h (x,y) where
    h (Compose fgac) = tabulate $ \(i,j) -> (index (index gfb j) i, index (index fgd i) j)
      where
       fgd :: f (g d)
       fgd = fmap (g . fmap snd) fgac
       gfb :: g (f b)
       gfb = tabulate $ \j -> f (fmap (\gac -> fst $ index gac j) fgac)

{-
  Hyper (f :: f a -> f b) x &&& Hyper (g :: g a -> g c) y = Hyper (Compose . h . getCompose) (x,y) where
    h :: Compose f g a -> Compose f g (b, c)
    h (Compose fga) = tabulate $ \(i,j) ->
      ( index f i (fmap (`index` j) fga)
      , index g j (index fga i)
      )
-}

instance Profunctor Hyper where
  dimap f g (Hyper h x) = Hyper (fmap g . h . fmap f) x

instance Strong Hyper where
  first' = first
  second' = second

instance Functor (Hyper a) where
  fmap f (Hyper h x) = Hyper (fmap f . h) x

-- |
-- @
-- 'base' = 'arr' . 'const'
-- @
base :: b -> Hyper a b
base b = Hyper (const (Identity b)) ()

-- | Unroll a hyperfunction
unroll :: Hyper a b -> (Hyper a b -> a) -> b
unroll (Hyper (f :: f a -> f b) x) k = index (f (tabulate (k . Hyper f))) x

-- | Re-roll a hyperfunction using Lambek's lemma.
roll :: ((Hyper a b -> a) -> b) -> Hyper a b
roll = Hyper (\ya xa2b -> xa2b (ya . unroll)) where

invoke :: Hyper a b -> Hyper b a -> b
invoke (Hyper (f :: f a -> f b) x) (Hyper (g :: g b -> g a) y) = index (index r x) y where
  r = tabulate $ \i -> tabulate $ \j -> index (f (fmap (\ gb -> index (g gb) j) r)) i

uninvoke :: (Hyper b a -> b) -> Hyper a b
uninvoke = Hyper $ \x f -> f (roll x)

-- |
-- @
-- 'arr' f ≡ 'push' f ('arr' f)
-- 'invoke' ('push' f q) k ≡ f ('invoke' k q)
-- 'push' f p . 'push' g q ≡ 'push' (f . g) (p . q)
-- @
push :: (a -> b) -> Hyper a b -> Hyper a b
push f q = uninvoke $ \k -> f (invoke k q)

-- |
-- @
-- 'run' f ≡ 'invoke' f 'id'
-- 'run' ('arr' f) = 'fix' f
-- 'run' ('push' f p . q) = f ('run' (q . p)) = f ('invoke' q p)
-- @
run :: Hyper a a -> a
run (Hyper f x) = index (fix f) x

-- |
-- @
-- 'project' . 'arr' ≡ 'id'
-- 'project' h a ≡ 'invoke' h ('base' a)
-- @
project :: Hyper a b -> a -> b
project (Hyper f x) a = index (f (tabulate (const a))) x

-- |
-- <http://arxiv.org/pdf/1309.5135.pdf Under "nice" conditions>
--
-- @
-- 'fold' . 'build' = 'id'
-- @
fold :: [a] -> (a -> b -> c) -> c -> Hyper b c
fold [] _ n = base n
fold (x:xs) c n = push (c x) (fold xs c n)

build :: (forall b c. (a -> b -> c) -> c -> Hyper b c) -> [a]
build g = run (g (:) [])
