{-# language GADTs #-}
module Data.Sigma where

data Sigma f where
  Sigma :: a -> f a -> Sigma f
