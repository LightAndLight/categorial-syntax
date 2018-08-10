{-# language GADTs #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
module Language.Category where

import Control.Applicative ((<|>))
import Control.Moore
import Data.Exists
import Data.Profunctor
import Data.Sigma

data Grammar c e
  = MkGrammar
  { infer :: String -> Maybe (Sigma c)
  , topLevel :: c e
  }

data Operator c where
  MkOperator :: c a -> c b -> (a -> b) -> Operator c

data Action c where
  Subgoals :: [Sigma c] -> Action c
  Operator :: Operator c -> Action c
  Operand :: Action c

mapAction :: (forall x. f x -> g x) -> Action f -> Action g
mapAction f (Subgoals a) = Subgoals $ (\(Sigma tm cat) -> Sigma tm (f cat)) <$> a
mapAction f (Operator (MkOperator a b g)) = Operator $ MkOperator (f a) (f b) g
mapAction _ Operand = Operand

class IsCategory c where
  is_ :: c a -> c b -> Maybe (a -> b)
  result_ :: c a -> Exists c
  step_ :: Sigma c -> Action c

mapCat :: (forall x. f x -> g x) -> Cat f a -> Cat g a
mapCat f (Many' a b) = Many' (mapCat f a) (mapCat f b)
mapCat f (Union' a b) = Union' (mapCat f a) (mapCat f b)
mapCat f (Arrow' a b) = Arrow' (mapCat f a) (mapCat f b)
mapCat _ (Exact' s) = Exact' s
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
  is_ a (Many' _ b') = (\f x -> constM (f x)) <$> is_ a b'
  is_ (Many' _ b) a' = (\f (Moore x _) -> f x) <$> is_ b a'
  is_ (Union' a b) c =
    (. fst) <$> is_ a c <|> (. snd) <$> is_ b c
  is_ a (Union' b c) =
    (\f g a' -> (f a', g a')) <$>
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

parse
  :: forall c e
   . IsCategory c
  => Grammar c e -- ^ Grammar specification
  -> [String] -- ^ Input
  -> [e]
parse grammar b = parse' b Nothing []
  where
    parse'
      :: IsCategory c
      => [String] -- ^ Input
      -> Maybe (Sigma c) -- ^ Current term
      -> [Operator c] -- ^ Operator stack
      -> [e]
    parse' [] (Just (Sigma tm cat)) [] =
      case is_ cat (topLevel grammar) of
        Nothing -> []
        Just f -> [f tm]
    parse' (i:input) Nothing operators =
      case infer grammar i of
        Nothing -> []
        Just v -> parse' input (Just v) operators
    parse' input (Just s@(Sigma tm cat)) operators =
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
                      Subgoals gs -> foldMap (\a -> parse' input (Just a) operators) gs
                      Operator op ->
                        parse' input Nothing (op : operators)
                      Operand ->
                        case operators of
                          [] -> []
                          MkOperator arg out f : operators' ->
                            case is_ cat arg of
                              Nothing -> []
                              Just h -> parse' input (Just $ Sigma (f $ h tm) out) operators'
    parse' [] Nothing _ = []
