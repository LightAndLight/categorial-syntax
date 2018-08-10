module Control.Moore where

import Data.Profunctor

data Moore a b = Moore b (a -> Moore a b)

instance Functor (Moore a) where
  fmap f = go
    where
      go (Moore b g) = Moore (f b) (go . g)

instance Profunctor Moore where
  dimap f g = go
    where
      go (Moore x y) = Moore (g x) (go . y . f)

constM :: b -> Moore a b
constM x = let val = Moore x (\_ -> val) in val

-- foldlM f b
--
-- MkMoore b $ \a =>
-- MkMoore (f b a) $ \a' =>
-- MkMoore (f (f b a) a') $ \a'' =>
-- MkMoore (f (f (f b a) a') a'') $ ...
foldlM :: (b -> a -> b) -> b -> Moore a b
foldlM f = go
  where
    go b = Moore b $ \a -> go (f b a)

-- foldrM f b
--
-- MkMoore b $ \a =>
-- MkMoore (f a b) $ \a' =>
-- MkMoore (f a (f a' b)) $ \a'' =>
-- MkMoore (f a (f a' (f a'' b))) $ ...
foldrM :: (a -> b -> b) -> b -> Moore a b
foldrM f = go
  where
    go b = Moore b $ \a -> go (f a b)
