{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language StandaloneDeriving #-}
{-# language UndecidableInstances #-}
module Data.Exists where

data Exists f where
  Exists :: f a -> Exists f
