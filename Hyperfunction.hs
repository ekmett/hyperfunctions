{-# LANGUAGE DeriveFunctor, RankNTypes, ScopedTypeVariables #-}
module Hyperfunctions where

import Control.Arrow
import Control.Category
import Data.Profunctor
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
data Hyper a b = Hyper { runHyper :: Hyper b a -> b }

instance Category Hyper where
  id = arr id
  Hyper f . g = Hyper (\k -> f (g . k))

instance Profunctor Hyper where
  dimap f g (Hyper h) = Hyper (g . h . dimap g f)

instance Arrow Hyper where
  arr f = r where r = push f r
{-
  first f = ana (go . peel) f where
    go :: ((Hyper b c -> b) -> c) -> (Hyper b c -> (b, d)) -> (c, d)
  first (Hyper f) = Hyper $ _ (f . Hyper) where
    go :: ((Hyper b c -> b) -> c) -> Hyper (c, d) (b, d) -> (c, d)
    go g (Hyper h) = (g _, undefined)
-}

ana :: (x -> (x -> a) -> b) -> x -> Hyper a b
ana g = f where
  f x = Hyper $ \(Hyper z) -> g x (z . f)

      -- h :: Hyper (b, d) (c, d) -> (b, d)
      -- g :: (Hyper b c -> b) -> c (bound at Hyperfunction.hs:27:8)
  

-- | 
-- @
-- push f p . push g q = push (f . g) (p . q)
-- @
push :: (a -> b) -> Hyper a b -> Hyper a b
push f q = Hyper $ \(Hyper k) -> f (k q)
  

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
run (Hyper f) = f id

-- |
-- 'project' is a left inverse for 'arr':
--
-- @
-- 'project' '.' 'arr' = 'id'
-- @
project :: Hyper a b -> a -> b
project (Hyper q) x = q (base x)

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

lh :: L a b -> Hyper a b
lh (L a as) = push a (lh as)

-- | An initial model of hyperfunctions
data L a b = L (a -> b) (L a b)

instance Category L where
  id = L id id
  L a as . L b bs = L (a . b) (as . bs)

instance Profunctor L where
  dimap f g (L a as) = L (dimap f g a) (dimap f g as)

instance Strong L where
  first' (L a as) = L (first' a) (first' as)
  second' (L a as) = L (second' a) (second' as)

instance Costrong L where
  unfirst (L a as) = L (unfirst a) (unfirst as)
  unsecond (L a as) = L (unsecond a) (unsecond as)

instance Choice L where
  left' (L a as) = L (left' a) (left' as)
  right' (L a as) = L (right' a) (right' as)

instance Arrow L where
  arr f = r where r = L f r
  first = first'
  second = second'
  L a as *** L b bs = L (a *** b) (as *** bs)
