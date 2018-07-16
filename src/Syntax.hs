{-# language GeneralizedNewtypeDeriving, OverloadedStrings #-}
{-# language OverloadedLists #-}
{-# language RecordWildCards #-}
{-# language LambdaCase #-}
{-# language GADTs #-}
{-# options_ghc -fwarn-incomplete-patterns #-}
module Syntax where

import Control.Monad.Fix (fix)
import Data.Char (isDigit, isLetter)
import Data.Either (rights, lefts)
import Data.Set (Set)
import Data.String (IsString)

import Data.Void

import qualified Data.Set as Set

newtype Symbol = Symbol String
  deriving (Eq, Ord, Show, IsString)

data Category
  = Expression
  | Atom
  | Exact Symbol
  | Union (Set Category)
  | Empty
  -- | OnL Category Category
  | OnR Category Category
  | Ident
  deriving (Eq, Show, Ord)

data Grammar
  = Grammar
  { infer :: Symbol -> Category
  , topLevel :: Category
  }

{-
[0-9]+       :   expression | atom | atom R-> expression
[a-zA-Z]+    :   expression | atom | feature(identifier) | atom R-> expression
'\'          :   f(identifier) R-> exact('.') R-> expression R-> expression
'('          :   expression R-> exact(')') R-> (expression | atom | atom R-> expression)

-}
lc :: Grammar
lc = Grammar{..}
  where
    infer s@(Symbol ds) | not (null ds), all isDigit ds = Union [Atom, fix $ \x -> OnR Atom (Union [Expression, x])]
    infer s@(Symbol cs) | not (null cs), all isLetter cs = Union [Ident, fix $ \x -> OnR Atom (Union [Expression, x])]
    infer s@(Symbol "\\") = OnR Ident (OnR (Exact ".") (OnR Expression Expression))
    infer s@(Symbol "(") = OnR Expression (OnR (Exact ")") (Union [Atom, fix $ \x -> OnR Atom (Union [Expression, x])]))
    infer s = Exact s

    topLevel = Expression

-- I think this is a subtyping relation
is :: Category -> Category -> Bool
is (OnR a b) (OnR a' b') = a' `is` a && b `is` b'
is Empty Union{} = True
is (Union as) (Union bs) = as `Set.isSubsetOf` bs
is a (Union as) = Set.member a as
is Atom Expression = True
is Ident Atom = True
is Ident Expression = True
is a b = a == b

isSentence :: Grammar -> [Symbol] -> Bool
isSentence g = go (topLevel g) [] Nothing
  where
    go goal [] Nothing [] = True
    go goal [] Nothing (s:ss) = go goal [infer g s] Nothing ss
    go goal [] (Just x) [] =
      case x of
        Union as -> or . fmap (\a -> go goal [] (Just a) []) $ Set.toList as
        _ -> x `is` goal
    go goal [] (Just x) (s:ss) = False
    go goal (Union as : operators) operand ss = or $ fmap (\a -> go goal (a : operators) operand ss) $ Set.toList as
    go goal os@(OnR a b : operators) Nothing (s:ss) = go goal (infer g s : os) Nothing ss
    go goal os@(OnR a b : operators) (Just op) ss =
      case op of
        Union as -> or . fmap (\a -> go goal os (Just a) ss) $ Set.toList as
        _ -> op `is` a && go goal (b:operators) Nothing ss
    go goal (a : operators) (Just op) ss = False
    go goal (a : operators) Nothing ss = go goal operators (Just a) ss
    -- go goal operators operand ss = error $ show (goal, operators, operand, ss)

data Expr = Lam String Expr | App Expr Expr | Var String
  deriving (Eq, Show)

{-
data Category'
  = Expression'
  | Atom'
  | Exact' Symbol
  | Union' (Set Category')
  | Empty'
  | OnR' Category' Category'
  | Ident' (String -> Expr)
  deriving (Eq, Show, Ord)

data Grammar'
  = Grammar'
  { infer' :: Symbol -> Category'
  , topLevel' :: Category'
  }

lc' :: Grammar'
lc' = Grammar'{..}
  where
    infer' s@(Symbol ds) | not (null ds), all isDigit ds = Union [Atom, fix $ \x -> OnR Atom (Union [Expression, x])]
    infer' s@(Symbol cs) | not (null cs), all isLetter cs = Union [Ident, fix $ \x -> OnR Atom (Union [Expression, x])]
    infer' s@(Symbol "\\") = OnR Ident (OnR (Exact ".") (OnR Expression Expression))
    infer' s@(Symbol "(") = OnR Expression (OnR (Exact ")") (Union [Atom, fix $ \x -> OnR Atom (Union [Expression, x])]))
    infer' s = Exact s

    topLevel' = Expression

parse :: Grammar -> [Symbol] -> Maybe Expr
parse g = go (topLevel g) [] Nothing
  where
    go goal [] Nothing [] = True
    go goal [] Nothing (s:ss) = go goal [infer g s] Nothing ss
    go goal [] (Just x) [] =
      case x of
        Union as -> or . fmap (\a -> go goal [] (Just a) []) $ Set.toList as
        _ -> x `is` goal
    go goal [] (Just x) (s:ss) = False
    go goal (Union as : operators) operand ss = or $ fmap (\a -> go goal (a : operators) operand ss) $ Set.toList as
    go goal os@(OnR a b : operators) Nothing (s:ss) = go goal (infer g s : os) Nothing ss
    go goal os@(OnR a b : operators) (Just op) ss =
      case op of
        Union as -> or . fmap (\a -> go goal os (Just a) ss) $ Set.toList as
        _ -> op `is` a && go goal (b:operators) Nothing ss
    go goal (a : operators) Nothing ss = go goal operators (Just a) ss
    go goal operators operand ss = error $ show (goal, operators, operand, ss)
-}
