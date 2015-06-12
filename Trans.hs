

-- fossacs2001 -- Categories of Processes Enriched in Final Coalgebras, Krstic, Launchbury and Pavlovic

newtype S s a b = S { runS :: a -> s -> (b, s) }

-- a -> (b * x)^s = store monad kleisli morphism
-- s -> a -> (s * x) -- for the functor f x = a -> (b * x)  -- an indexed store monad kleisli morphism

instance Category (S s)
instance Profunctor (S s)
instance Choice (S s)
instance Strong (S s)
instance Sieve (S s) (State s)
instance Representable (S s)
instance Functor (S s a)
instance Applicative (S s a)
instance Monad (S s a) 
instance Arrow (S s)
instance ArrowApply (S s)
instance ArrowChoice (S s)
instance ArrowLoop (S s) -- based on the MonadFix instance?

-- unique homomorphism to the final coalgebra [A,B]_R of the functor R x = a -> (b, x)
mealy :: S s a b -> s -> Mealy a b

newtype Mealy a b = Mealy (a -> (b, Mealy a b))

-- MealyT m a b = a -> m (b, MealyT m a b)

-- elements of [A,B]_R (Mealy machines) are known as resumptions

newtype MealyT a b = MealyT { runMealyT :: a -> m (b, MealyT a b) }

newtype F s a b = F { runF :: (s -> a) -> s -> b }

-- (x -> a, x) -> b -- a cokleisli morphism for store
-- a coalgebra x -> b^a^x for the functor x -> (x -> a) -> b
 
instance Functor (F s a)
instance Category (F s) 
instance Choice (F s)
instance Arrow (F s)
instance Cosieve (F s) (Store s)
instance Corepresentable (F s)
instance ArrowLoop (F s) -- can we comonad fix point to find a nice fixed point here?

-- unique homomorphism to the final coalgebra [A,B]_H of the functor H a b x = (x -> a) -> b

-- ana ::(x -> (x -> a) -> b) -> x -> Hyper a b

newtype Hyper a b = Hyper { runHyper :: (Hyper a b -> a) -> b }

-- newtype HyperT w a b = HyperT { runHyperT :: w (HyperT w a b -> a) -> b }

-- Categories of Processes Enriched in Initial Algebras -- er.. me, right now

data C s a b = C { runC :: (b -> s) -> (a -> s) }

instance Functor (C s a)
instance Monad (C s)
instance Category (C s)
instance Sieve (C s) (Cont s)
instance Representable (C s)
instance Arrow (C s)
instance Profunctor (C s)
instance Strong (C s)
instance Choice (C s)

-- 
