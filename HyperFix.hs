{-# LANGUAGE DeriveFunctor, RankNTypes, ScopedTypeVariables #-}
module Hyperfunctions where

import Control.Applicative
import Control.Arrow
import Control.Category
import Control.Monad.Fix
import Data.Coerce
import Data.Profunctor
import Data.Profunctor.Unsafe
import Prelude hiding ((.),id)

-- |
--
-- @
-- 'runHyper' f g = 'run' (f . g)
-- 'arr' f = 'push' f ('arr' f)
-- 'runHyper' id id = _|_
-- @
--
-- 'arr' is a faithful functor, so
--
-- @'arr' f ≡ 'arr' g@ implies @f ≡ g@ 
--
newtype Hyper a b = Hyper { runHyper :: Hyper b a -> b }

ana :: (x -> (x -> a) -> b) -> x -> Hyper a b
ana g = f where f x = Hyper $ \z -> g x (runHyper z . f)

unroll :: Hyper a b -> (Hyper a b -> a) -> b
unroll = coerce

instance Category Hyper where
  id = arr id
  f . g = Hyper $ \k -> runHyper f (g . k)

instance Profunctor Hyper where
  dimap f g h = Hyper $ g . runHyper h . dimap g f
  lmap f h = Hyper $ runHyper h . rmap f
  rmap f h = Hyper $ f . runHyper h . lmap f

instance Arrow Hyper where
  arr = fix . push
  first = ana $ \i fac -> (unroll i (fst . fac), snd (fac i))
  second = ana $ \i fca -> (fst (fca i), unroll i (snd . fca))
  (***) = curry $ ana $ \(i,j) fgac -> (unroll i $ \i' -> fst $ fgac (i',j), unroll j $ \j' -> snd $ fgac (i,j'))
  (&&&) = curry $ ana $ \(i,j) fga  -> (unroll i $ \i' ->       fga  (i',j), unroll j $ \j' ->       fga  (i,j'))

instance Strong Hyper where
  first' = first
  second' = second

instance Functor (Hyper a) where
  fmap = rmap

instance Applicative (Hyper a) where
  pure = arr . const
  p <* _ = p
  _ *> p = p
  (<*>) = curry $ ana $ \(i,j) fga ->
    unroll i (\i' -> fga (i',j)) $ unroll j (\j' -> fga (i,j'))

-- | 
-- @
-- push f p . push g q = push (f . g) (p . q)
-- @
push :: (a -> b) -> Hyper a b -> Hyper a b
push f q = Hyper $ \k -> f (runHyper k q)
  

-- |
--
-- @
-- base = arr . const
-- @
base :: a -> Hyper b a
base p = Hyper $ \_ -> p

-- | 
--
-- @
-- run ('arr' f) = 'fix' f
-- run ('push' f p . q) = f ('run' (q . p)) = f ('runHyper' q p)
-- @
run :: Hyper a a -> a
run f = runHyper f id

-- |
-- 'project' is a left inverse for 'arr':
--
-- @
-- 'project' '.' 'arr' = 'id'
-- @
project :: Hyper a b -> a -> b
project q x = runHyper q (base x)

fold :: [a] -> (a -> b -> c) -> c -> Hyper b c
fold xs c n = foldr (push . c) (base n) xs

-- | 
-- <http://arxiv.org/pdf/1309.5135.pdf Under nice conditions>
--
-- @
-- 'fold' . 'build' = 'id'
-- @
build :: (forall b c. (a -> b -> c) -> c -> Hyper b c) -> [a]
build g = run (g (:) [])
