{-# language GADTs, ExistentialQuantification #-}
{-# language FlexibleContexts, UndecidableInstances #-}
{-# language ScopedTypeVariables #-}
{-# language FlexibleInstances, StandaloneDeriving #-}
{-# language RankNTypes #-}
{-# options_ghc -fwarn-incomplete-patterns #-}
-- module Syntax where
module Main where

import Control.Applicative ((<|>))
import Data.Char (isLetter, isDigit)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Semigroup (Semigroup, (<>))

import qualified Data.List.NonEmpty as NonEmpty

import Debug.Trace

main :: IO ()
main = do
  print $ parse lc' $ words $ "a 1" 
  print $ parse2 lc' $ words $ "a 1" 
  print $ parse lc' $ words $ "a \\ x . x" 
  print $ parse2 lc' $ words $ "a \\ x . x" 
  print $ parse lc' $ words $ "a b c"
  print $ parse2 lc' $ words $ "a b c"
  print $ parse lc' $ words $ "a ( b c d ) e"
  print $ parse2 lc' $ words $ "a ( b c d ) e"
  print $ parse lc' $ words $
    "a b c d e f g h i j k l m n o p q r s t u v w x y z " ++
    "a b c d e f g h i j k l m n o p q r s t u v w x y z" ++
    "a b c d e f g h i j k l m n o p q r s t u v w x y z"
  print $ parse2 lc' $ words $
    "a b c d e f g h i j k l m n o p q r s t u v w x y z " ++
    "a b c d e f g h i j k l m n o p q r s t u v w x y z" ++
    "a b c d e f g h i j k l m n o p q r s t u v w x y z"
  print $ parse lc' $ words "\\ x . x"
  print $ parse2 lc' $ words "\\ x . x"

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

data Expr
  = Lam String Expr
  | App Expr Expr
  | V String
  | I Int
  deriving (Eq, Show)

data Operator c where
  MkOperator :: c a -> c b -> (a -> b) -> Operator c

data Action c where
  Subgoals :: [Sigma c] -> Action c
  Operator :: Operator c -> Action c
  Operand :: Action c

mapAction :: (forall x. f x -> g x) -> Action f -> Action g
mapAction f (Subgoals a) = Subgoals $ (\(Sigma tm cat) -> Sigma tm (f cat)) <$> a
mapAction f (Operator (MkOperator a b g)) = Operator $ MkOperator (f a) (f b) g
mapAction f Operand = Operand

class IsCategory c where
  is_ :: c a -> c b -> Maybe (a -> b)
  result_ :: c a -> Exists c
  step_ :: Sigma c -> Action c

mapCat :: (forall x. f x -> g x) -> Cat f a -> Cat g a
mapCat f (Many' a b) = Many' (mapCat f a) (mapCat f b)
mapCat f (Union' a b) = Union' (mapCat f a) (mapCat f b)
mapCat f (Arrow' a b) = Arrow' (mapCat f a) (mapCat f b)
mapCat f (Exact' s) = Exact' s
mapCat f (C' a) = C' (f a)

data Cat c a where
  Many' :: Cat c a -> Cat c b -> Cat c (Moore a b)
  Union' :: Cat c a -> Cat c b -> Cat c (a, b)
  Arrow' :: Cat c a -> Cat c b -> Cat c (a -> b)
  Exact' :: String -> Cat c String
  C' :: c a -> Cat c a

instance IsCategory c => IsCategory (Cat c) where
  is_ (Exact' s) (Exact' s')
    | s == s' = Just id
    | otherwise = Nothing
  is_ (Many' a b) (Many' a' b') =
    dimap <$>
    is_ a' a <*>
    is_ b b'
  is_ a (Many' a' b') = (\f x -> constM (f x)) <$> is_ a b'
  is_ (Many' a b) a' = (\f (Moore x _) -> f x) <$> is_ b a'
  is_ (Union' a b) c =
    (. fst) <$> is_ a c <|> (. snd) <$> is_ b c
  is_ a (Union' b c) =
    (\f g a -> (f a, g a)) <$>
    is_ a b <*>
    is_ a c
  is_ (Arrow' a b) (Arrow' a' b') =
    (\f g h -> g . h . f) <$>
    is_ a' a <*>
    is_ b b'
  is_ (C' a) (C' b) = is_ a b
  is_ _ _ = Nothing

  result_ (Union' a b) =
    case result_ a of
      Exists a' ->
        case result_ b of
          Exists b' -> Exists (Union' a' b')
  result_ (Arrow' _ b) = result_ b
  result_ (Many' _ b) = result_ b
  result_ (C' e) =
    case result_ e of
      Exists e' -> Exists (C' e')
  result_ a = Exists a

  step_ (Sigma tm cat) =
    case cat of
      Arrow' a b -> Operator $ MkOperator a b tm
      Union' a b -> Subgoals [Sigma (fst tm) a, Sigma (snd tm) b]
      Many' a b ->
        let Moore v rest = tm in Subgoals [Sigma (v, rest) (Union' b (Arrow' a cat))]
      C' a ->
        mapAction C' $ step_ (Sigma tm a)
      _ -> Operand

instance IsCategory Category where
  is_ = is
  result_ = result
  step_ (Sigma tm cat) =
    case cat of
      Arrow a b -> Operator $ MkOperator a b tm
      Union a b -> Subgoals [Sigma (fst tm) a, Sigma (snd tm) b]
      Many a b ->
        let Moore v rest = tm in Subgoals [Sigma (v, rest) (Union b (Arrow a cat))]
      _ -> Operand

data SExp = Nil | Cons SExp SExp | Str String deriving (Eq, Show)

data SC a where
  AtomC :: SC SExp

sexp :: Grammar (Cat SC) SExp
sexp = MkGrammar infer' (C' AtomC)
  where
    infer' :: String -> Maybe (Sigma (Cat SC))
    infer' str
      | all isLetter str = Just $ Sigma (Str str) (C' AtomC)
      | otherwise =
          case str of
            "(" ->
              Just $
              Sigma
                (foldrM (\a b s -> Cons a (b s)) (\_ -> Nil))
                (Many' (C' AtomC) (Arrow' (Exact' ")") (C' AtomC)))
            _ -> Just $ Sigma str (Exact' str)

instance IsCategory SC where
  is_ AtomC AtomC = Just id
  result_ AtomC = Exists AtomC
  step_ (Sigma _ AtomC) = Operand

data Category a where
  Expression :: Category Expr
  Atom :: Category Expr
  Ident :: Category String
  Exact :: String -> Category String
  Union :: Category a -> Category b -> Category (a, b)
  Arrow :: Category a -> Category b -> Category (a -> b)
  Many :: Category a -> Category b -> Category (Moore a b)
deriving instance Show (Category a)

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
instance Show (Sigma Category) where
  show (Sigma _ b) = show b

data Exists f = forall a. Exists (f a)
deriving instance Show (Exists Category)

result :: Category a -> Exists Category
result (Union a b) =
  case result a of
    Exists a' ->
      case result b of
        Exists b' -> Exists (Union a' b')
result (Arrow _ b) = result b
result (Many _ b) = result b
result e = Exists e

data Grammar c e
  = MkGrammar
  { infer :: String -> Maybe (Sigma c)
  , topLevel :: c e
  }

{-
goal:          A
inferences:    "a" : Union A (A -> Many A A)
input:          ["a", "a"]
term:           []
operator_stack: []
operand_stack:  []

goal:           A
inferences:     "a" : Union A (A -> Many A A)
input:          ["a"]
term:           [Union A (A -> Many A A)]
operator_stack: []
operand_stack:  []

goal:           A
inferences:     "a" : Union A (A -> Many A A)
input:          ["a"] ["a"]
term:           [A]   [A -> Many A A]
operator_stack: []    []
operand_stack:  []    []

goal:           A
inferences:     "a" : Union A (A -> Many A A)
input:          fail ["a"]
term:           fail []
operator_stack: fail []
operand_stack:  fail [A -> Many A A]

goal:           A
inferences:     "a" : Union A (A -> Many A A)
input:          []
term:           [Union A (A -> Many A A)]
operator_stack: []
operand_stack:  [A -> Many A A]

goal:           A
inferences:     "a" : Union A (A -> Many A A)
input:          []              []
term:           [A]             [A -> Many A A]
operator_stack: []              [A -> Many A A]
operand_stack:  [A -> Many A A] []

goal:           A
inferences:     "a" : Union A (A -> Many A A)
input:          []              []
term:           []              []
operator_stack: [A]             [A -> Many A A, A -> Many A A]
operand_stack:  [A -> Many A A] []

goal:           A
inferences:     "a" : Union A (A -> Many A A)
input:          []              fail
term:           []              fail
operator_stack: [A]             fail
operand_stack:  [A -> Many A A] fail

goal:           A
inferences:     "a" : Union A (A -> Many A A)
input:          []
term:           [Many A A]
operator_stack: []
operand_stack:  []

goal:           A
inferences:     "a" : Union A (A -> Many A A)
input:          []
term:           [Union A (A -> Many A A)]
operator_stack: []
operand_stack:  []

goal:           A
inferences:     "a" : Union A (A -> Many A A)
input:          []  []
term:           [A] [A -> Many A A]
operator_stack: []  []
operand_stack:  []  []

goal:           A
inferences:     "a" : Union A (A -> Many A A)
input:          []  []
term:           []  []
operator_stack: []  [A -> Many A A]
operand_stack:  [A] []

goal:           A
inferences:     "a" : Union A (A -> Many A A)
input:          success fail
term:           success fail
operator_stack: success fail
operand_stack:  success fail
-}

parse2
  :: IsCategory c
  => Grammar c e -- ^ Grammar specification
  -> [String] -- ^ Input
  -> [e]
parse2 a b = parse' a b Nothing []
  where
    parse'
      :: IsCategory c
      => Grammar c e -- ^ Grammar specification
      -> [String] -- ^ Input
      -> Maybe (Sigma c) -- ^ Current term
      -> [Operator c] -- ^ Operator stack
      -> [e]
    parse' grammar [] (Just (Sigma tm cat)) [] =
      case is_ cat (topLevel grammar) of
        Nothing -> []
        Just f -> [f tm]
    parse' grammar (i:input) Nothing operators =
      case infer grammar i of
        Nothing -> []
        Just v -> parse' grammar input (Just v) operators
    parse' grammar input (Just s@(Sigma tm cat)) operators =
      let
        goal =
          case operators of
            [] -> Exists $ topLevel grammar
            MkOperator a _ _ : _ -> Exists a
      in
        case goal of
          Exists goal' ->
            case result_ cat of
              Exists res ->
                case is_ res goal' of
                  Nothing ->
                    []
                  Just{} ->
                    case step_ s of
                      Subgoals gs -> foldMap (\a -> parse' grammar input (Just a) operators) gs
                      Operator op ->
                        parse' grammar input Nothing (op : operators)
                      Operand ->
                        case operators of
                          [] -> []
                          MkOperator arg out f : operators' ->
                            case is_ cat arg of
                              Nothing -> []
                              Just h -> parse' grammar input (Just $ Sigma (f $ h tm) out) operators'
    parse' _ [] Nothing _ = []

parse
  :: Grammar Category e -- ^ Grammar specification
  -> [String] -- ^ Input
  -> [e]
parse a b = parse' a b Nothing []
  where
    parse'
      :: Grammar Category e -- ^ Grammar specification
      -> [String] -- ^ Input
      -> Maybe (Sigma Category) -- ^ Current term
      -> [Sigma Category] -- ^ Operator stack
      -> [e]
    parse' grammar [] (Just (Sigma tm cat)) [] =
      case is cat (topLevel grammar) of
        Nothing -> []
        Just f -> [f tm]
    parse' grammar (i:input) Nothing operators =
      case infer grammar i of
        Nothing -> []
        Just v -> parse' grammar input (Just v) operators
    parse' grammar input (Just (Sigma tm cat)) operators =
      let
        goal =
          case operators of
            [] -> Exists $ topLevel grammar
            Sigma _ (Arrow a _) : _ -> Exists a
            _ -> error "operand on operator stack"
      in
        -- case traceShow ("expand", input, Sigma tm cat, operators) goal of
        case goal of
          Exists goal' ->
            case result cat of
              Exists res ->
                case is res goal' of
                  Nothing ->
                    -- traceShow ("expandFailed", res, goal') []
                    []
                  Just{} ->
                    case cat of
                      Union a b ->
                        parse' grammar input (Just (Sigma (fst tm) a)) operators <>
                        parse' grammar input (Just (Sigma (snd tm) b)) operators
                      Many a b ->
                        let
                          Moore v rest = tm
                        in
                          parse' grammar input (Just (Sigma (v, rest) (Union b (Arrow a cat)))) operators
                      Arrow{} -> parse' grammar input Nothing (Sigma tm cat : operators)
                      _ ->
                        case operators of
                          [] -> [] -- parse' grammar input Nothing operators (Sigma tm cat:operands)
                          operator : operators' ->
                            -- case traceShow ("apply", input, Sigma tm cat, operator:operators') operator of
                            case operator of
                              Sigma f (Arrow a b) ->
                                case is cat a of
                                  Nothing -> []
                                    -- traceShow ("applyFail", Sigma tm cat, operator:operators, Sigma tm cat:operands) []
                                  Just h -> parse' grammar input (Just $ Sigma (f $ h tm) b) operators'
                              _ -> error "operand on operator stack"
    parse' _ [] Nothing _ = []

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

lc' :: Grammar Category Expr
lc' = MkGrammar infer' Expression
  where
    infer' :: String -> Maybe (Sigma Category)
    infer' cs
      | all isDigit cs =
          Just $
            Sigma
              ( let val = I (read cs) in
                ( val
                , \e -> foldlM App (App val e)
                )
              )
              (Union Atom (Arrow Atom (Many Atom Expression)))
      | all isLetter cs =
          Just $
            Sigma
              ( cs, \e -> foldlM App (App (V cs) e))
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
                  (\e _ -> (e, \e' -> foldlM App (App e e')))
                  (Arrow
                    Expression
                    (Arrow
                        (Exact ")")
                        (Union Atom
                         (Arrow Atom (Many Atom Expression)))))
            _ -> Just $ Sigma cs (Exact cs)
