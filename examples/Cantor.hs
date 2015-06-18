{-# LANGUAGE RankNTypes #-}
module Cantor 
  ( _Natural
  ) where

import Control.Monad.Hyper
import Data.Profunctor
import Numeric.Natural

-- <http://math.andrej.com/2009/10/12/constructive-gem-double-exponentials/>

data UCF
  = Const Bool
  | NonConst UCF'

data UCF'
  = Head Bool
  | And Bool UCF'
  | Or Bool UCF'
  | Decompose UCF' UCF'

type Cantor = Natural -> Bool
type Functional = Cantor -> Bool

find :: Functional -> Cantor
find p = branch x0 l0 (find (\r -> p (branch x0 l0 r)))
  where
    branch x _ _ 0 = x
    branch _ l r n
      | odd n = l ((n - 1) `div` 2)
      | otherwise = r ((n - 2) `div` 2)

    x0 = forsome (\l -> forsome (\r -> p (branch True l r)))
    l0 = find (\l -> forsome (\r -> p (branch x0 l r)))

forevery, forsome :: Functional -> Bool
forsome f = f (find f)
forevery f = not (forsome (not . f))

getConst :: Functional -> Maybe Bool
getConst f 
  | forevery (\a -> f a == b) = Just b
  | otherwise = Nothing
  where b = f (const False)
    
prepend :: Bool -> Cantor -> Cantor
prepend b _ 0 = b
prepend _ a n = a (n-1)

shift :: Bool -> Functional -> Functional
shift b f = f . prepend b

unfn :: Functional -> UCF 
unfn f0 = case getConst f0 of
  Just b -> Const b
  Nothing -> NonConst (unfn' f0)
    where
      sf = shift False
      st = shift True
      unfn' :: Functional -> UCF'
      unfn' f = case getConst (sf f) of
        Nothing -> case getConst (st f) of
          Nothing -> Decompose (unfn' (sf f)) (unfn' (st f))
          Just False -> And False (unfn' (sf f))
          Just True -> Or True (unfn' (sf f))
        Just False -> case getConst (st f) of
          Nothing -> And True (unfn' (st f))
          Just False -> error "impossible"
          Just True -> Head True
        Just True -> case getConst (st f) of
          Nothing -> Or False (unfn' (st f))
          Just False -> Head False
          Just True -> error "impossible"

pair :: Natural -> Natural -> Natural
pair 0 0 = 0
pair m n = mr + 2 * nr + 4 * pair mq nq where
  (mq, mr) = divMod m 2
  (nq, nr) = divMod n 2

unpair :: Natural -> (Natural, Natural)
unpair 0 = (0, 0)
unpair n = (xr + 2*x, yr + 2*y) where
  (p, xr) = divMod n 2
  (q, yr) = divMod p 2
  (x, y) = unpair q

enum :: Natural -> Functional
enum 0 = const False
enum 1 = const True
enum n0 = fn' (n0-2) where
  fn' f a = compute 0 f where
    compute k 0 = not (a k)
    compute k 1 = a k
    compute k n | n' <- n - 2, q <- div n' 5 = case mod n' 5 of
      0 -> not (a k) && compute (k+1) q
      1 -> a k && compute (k+1) q
      2 -> not (a k) || compute (k+1) q
      3 -> a k || compute (k+1) q
      _ | (n1, n2) <- unpair q -> if a k
         then compute (k+1) n1
         else compute (k+1) n2

denum :: UCF -> Natural
denum (Const False) = 0
denum (Const True) = 1
denum (NonConst x0) = 2 + denum' x0 where
  denum' (Head False) = 0
  denum' (Head True) = 1
  denum' (And False x) = 2 + 5 * denum' x
  denum' (And True x) = 3 + 5 * denum' x
  denum' (Or False x) = 4 + 5 * denum' x
  denum' (Or True x) = 5 + 5 * denum' x
  denum' (Decompose x y) = 6 + 5 * pair (denum' x) (denum' y)

type Iso' s a = forall p f. (Profunctor p, Functor f) => p a (f a) -> p s (f s)

-- | Inductive Hyper functions from Bool to Bool are isomorphic to the natural numbers.
_Natural :: Iso' Natural (Hyper Bool Bool)
_Natural = dimap (ana enum) (fmap (cata (denum . unfn)))
