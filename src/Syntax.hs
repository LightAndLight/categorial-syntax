{-# language GADTs, ExistentialQuantification #-}
{-# language ScopedTypeVariables #-}
{-# options_ghc -fwarn-incomplete-patterns #-}
-- module Syntax where
module Main where

import Control.Applicative ((<|>))
import Data.Char (isLetter, isDigit)
import Data.Semigroup (Semigroup, (<>))

main :: IO ()
main =
  print $ parse lc' $ words "a b c d e f g h i j k l m n o p q r"

data Moore a b = Moore b (a -> Moore a b)

instance Functor (Moore a) where
  fmap f = go
    where
      go (Moore b g) = Moore (f b) (go . g)

dimap :: (a' -> a) -> (b -> b') -> Moore a b -> Moore a' b'
dimap f g = go
  where
    go (Moore x y) = Moore (g x) (go . y . f)

constM :: b -> Moore a b
constM x = let val = Moore x (\_ -> val) in val

data Expr = Lam String Expr | App Expr Expr | V String | I Int deriving (Eq, Show)

data Category a where
  Expression :: Category Expr
  Atom :: Category Expr
  Ident :: Category String
  Exact :: String -> Category String
  Union :: Category a -> Category b -> Category (a, b)
  Arrow :: Category a -> Category b -> Category (a -> b)
  Many :: Category a -> Category b -> Category (Moore a b)

is :: Category a -> Category b -> Maybe (a -> b)
is Expression Expression = Just id
is Atom Expression = Just id
is Atom Atom = Just id
is Ident Ident = Just id
is Ident Atom = Just V
is Ident Expression = Just V
is (Exact s) (Exact s') | s == s' = Just id
is (Many a b) (Many a' b') =
  dimap <$>
  is a' a <*>
  is b b'
is a (Many a' b') = (\f x -> constM (f x)) <$> is a b'
is (Many a b) a' = (\f (Moore x _) -> f x) <$> is b a'
is (Union a b) c =
  (. fst) <$> is a c <|> (. snd) <$> is b c
is a (Union b c) =
  (\f g a -> (f a, g a)) <$>
  is a b <*>
  is a c
is (Arrow a b) (Arrow a' b') =
  (\f g h -> g . h . f) <$>
  is a' a <*>
  is b b'
is _ _ = Nothing

data Sigma f = forall a. Sigma a (f a)

data Grammar e
  = MkGrammar
  { infer :: String -> Maybe (Sigma Category)
  , topLevel :: Category e
  }

parse :: forall e. Grammar e -> [String] -> [e]
parse (MkGrammar doInfer goal) = go []
  where
    go ::
      [Sigma Category] ->
      [String] ->
      [e]
    go (Sigma tm (Union a b) : ks) xs =
      go (Sigma (fst tm) a : ks) xs <>
      go (Sigma (snd tm) b : ks) xs
    go (Sigma tm (Many a b) : ks) xs =
      case tm of
        Moore v f ->
          go (Sigma v b : ks) xs <>
          go (Sigma f (Arrow a $ Many a b) : ks) xs
    go [Sigma tm cat] [] =
      case is cat goal of
        Nothing -> mempty
        Just f -> [f tm]
    go (Sigma tm cat : Sigma tm' (Arrow a b) : ks) xs
      | Just f <- is cat a =
          go (Sigma (tm' $ f tm) b : ks) xs
    go ks (c : cs) =
      case doInfer c of
        Nothing -> mempty
        Just v -> go (v : ks) cs
    go ks [] = mempty

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

testGrammar :: Grammar Expr
testGrammar = MkGrammar infer' Expression
  where
    infer' :: String -> Maybe (Sigma Category)
    infer' a = Just $ Sigma (foldlM App (V a)) (Many Expression Expression)

lc' :: Grammar Expr
lc' = MkGrammar infer' Expression
  where
    infer' :: String -> Maybe (Sigma Category)
    infer' cs
      | all isDigit cs =
          Just $
            Sigma
              ( let val = I (read cs) in
                ( val
                , \e -> ($ val) <$> foldlM (\x y -> \z -> App (x z) y) (`App` e)
                )
              )
              (Union Atom (Arrow Atom (Many Atom Expression)))
      | all isLetter cs =
          Just $
            Sigma
              ( cs, \e -> ($ V cs) <$> foldlM (\x y -> \z -> App (x z) y) (`App` e) )
              (Union Ident (Arrow Atom (Many Atom Expression)))
      | otherwise =
          case cs of
            "\\" ->
              Just $
                Sigma
                  (\x _ e -> Lam x e)
                  (Arrow Ident (Arrow (Exact ".") (Arrow Expression Expression)))
            "(" ->
              Just $
                Sigma
                  (\e _ -> foldlM App e)
                  (Arrow
                    Expression
                    (Arrow
                        (Exact ")")
                        (Many
                          Atom
                          Expression)))
            _ -> Just $ Sigma cs (Exact cs)
