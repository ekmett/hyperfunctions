{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
module RepresentableHyperfunctions where

import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Rep
import Data.Profunctor
import Data.Profunctor.Unsafe
import Control.Arrow
import Control.Category
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
  Hyper :: Representable g => g (g a -> b) -> Rep g -> Hyper a b

instance Category Hyper where
  id = Hyper (Identity runIdentity) ()
  Hyper f x . Hyper g y = Hyper
    (Compose $ fmap (\phi -> fmap (\psi -> phi . fmap psi . getCompose) g) f)
    (x,y)

instance Arrow Hyper where
  arr f = Hyper (Identity (f .# runIdentity)) ()

  first (Hyper (f :: f (f a -> b)) x) = Hyper f' x where
    f' :: forall c. f (f (a,c) -> (b,c))
    f' = tabulate $ \i fac -> (index f i (fmap fst fac), snd (index fac i))

  second (Hyper (f :: f (f a -> b)) x) = Hyper f' x where
    f' :: forall c. f (f (c,a) -> (c,b))
    f' = tabulate $ \i fca -> (fst (index fca i), index f i (fmap snd fca))

  Hyper (f :: f (f a -> b)) x *** Hyper (g :: g (g c -> d)) y = Hyper h (x,y) where
    h :: Compose f g (Compose f g (a,c) -> (b, d))
    h = tabulate $ \(i,j) (Compose fgac) ->
      ( index f i (fmap (\gac -> fst (index gac j)) fgac)
      , index g j (fmap snd (index fgac i))
      )

  Hyper (f :: f (f a -> b)) x &&& Hyper (g :: g (g a -> c)) y = Hyper h (x,y) where
    h :: Compose f g (Compose f g a -> (b, c))
    h = tabulate $ \(i,j) (Compose fga) ->
      ( index f i (fmap (`index` j) fga)
      , index g j (index fga i)
      )

instance Profunctor Hyper where
  dimap f g (Hyper h x) = Hyper (fmap (\fa2b -> g . fa2b . fmap f) h) x

instance Strong Hyper where
  first' = first
  second' = second

instance Functor (Hyper a) where
  fmap f (Hyper h x) = Hyper (fmap (f .) h) x

-- |
-- @
-- 'base' = 'arr' . 'const'
-- @
base :: b -> Hyper a b
base b = Hyper (Identity (const b)) ()

-- |
-- @
-- 'arr' f ≡ 'push' f ('arr' f)
-- 'invoke' ('push' f q) k ≡ f ('invoke' k q)
-- 'push' f p . 'push' g q ≡ 'push' (f . g) (p . q)
-- @
push :: (a -> b) -> Hyper a b -> Hyper a b
push f q = uninvoke $ \k -> f (invoke k q)

-- | Unroll a hyperfunction
unroll :: Hyper a b -> (Hyper a b -> a) -> b
unroll (Hyper (f :: f (f a -> b)) x) k = index f x (tabulate (k . Hyper f))

-- | Re-roll a hyperfunction using Lambek's lemma.
roll :: ((Hyper a b -> a) -> b) -> Hyper a b
roll = Hyper (mapH unroll)

mapH :: (x -> y) -> ((x -> a) -> b) -> (y -> a) -> b
mapH xy xa2b ya = xa2b (ya . xy)

invoke :: Hyper a b -> Hyper b a -> b
invoke (Hyper (f :: f (f a -> b)) x) (Hyper (g :: g (g b -> a)) y) = index (index r x) y where
  -- tie a knot through state space
  r = fmap (\phi -> fmap (\psi -> phi (fmap psi r)) g) f

uninvoke :: (Hyper b a -> b) -> Hyper a b
uninvoke = Hyper (. roll)

-- |
-- @
-- 'run' f ≡ 'invoke' f 'id'
-- 'run' ('arr' f) = 'fix' f
-- 'run' ('push' f p . q) = f ('run' (q . p)) = f ('invoke' q p)
-- @
run :: Hyper a a -> a
run (Hyper f x) = index r x where r = fmap (\phi -> phi r) f

-- |
-- @
-- 'project' . 'arr' ≡ 'id'
-- 'project' h a ≡ 'invoke' h ('base' a)
-- @
project :: Hyper a b -> a -> b
project (Hyper f x) a = index f x (tabulate (const a))

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