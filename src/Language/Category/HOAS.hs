{-# language GADTs #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
module Language.Category.HOAS
  ( Expr(..)
  , QExpr(..)
  , eval
  , ESigma(..)
  , Grammar(..)
  , Cat(..)
  , IsCategory(..)
  , Operator(..)
  , Action(..)
  , parse
  )
where

import Control.Applicative ((<|>))
import Control.Moore (Moore)
import Data.Exists

import qualified Control.Moore

import Language.Category
  hiding
  ( IsCategory(..)
  , Grammar(..)
  , Operator(..)
  , Action(..)
  , mapAction
  , parse
  )

data ESigma var f = forall a. ESigma (Expr var a) (f a)

data QExpr var a where
  QVar :: var a -> QExpr var a
  QLam :: (var a -> QExpr var b) -> QExpr var (a -> b)
  QApp :: QExpr var (a -> b) -> QExpr var a -> QExpr var b

  QPair :: QExpr var a -> QExpr var b -> QExpr var (a, b)
  QFst :: QExpr var ((a, b) -> a)
  QSnd :: QExpr var ((a, b) -> b)

  QFix :: (var a -> QExpr var a) -> QExpr var a

  QMoore :: QExpr var ((b, a -> Moore a b) -> Moore a b)
  QUnMoore :: QExpr var (Moore a b -> (b, a -> Moore a b))

data Expr var a where
  Var :: var a -> Expr var a
  Lam :: (var a -> Expr var b) -> Expr var (a -> b)
  App :: Expr var (a -> b) -> Expr var a -> Expr var b

  Pair :: Expr var a -> Expr var b -> Expr var (a, b)
  Fst :: Expr var ((a, b) -> a)
  Snd :: Expr var ((a, b) -> b)

  Fix :: (var a -> Expr var a) -> Expr var a

  Moore :: Expr var ((b, a -> Moore a b) -> Moore a b)
  UnMoore :: Expr var (Moore a b -> (b, a -> Moore a b))

  Quote :: QExpr var a -> Expr var (Expr var a)
  Unquote :: Expr var (Expr var a) -> Expr var a

newtype Var a = MkVar a

unquote :: QExpr var a -> Expr var a
unquote (QVar v) = Var v
unquote (QLam f) = Lam (unquote . f)
unquote (QApp a b) = App (unquote a) (unquote b)
unquote QFst = Fst
unquote QSnd = Snd
unquote (QFix f) = Fix (unquote . f)
unquote QMoore = Moore
unquote QUnMoore = UnMoore

eval :: (forall var. Expr var a) -> a
eval = go
  where
    go :: Expr Var a -> a
    go (Var (MkVar a)) = a
    go (Lam f) = \a -> go (f (MkVar a))
    go (App f x) = go f (go x)
    go (Pair a b) = (go a, go b)
    go Fst = fst
    go Snd = snd
    go (Fix f) = let x = go $ f (MkVar x) in x
    go Moore = \(a, b) -> Control.Moore.Moore a b
    go UnMoore = \(Control.Moore.Moore a b) -> (a, b)
    go (Unquote a) = go (go a)
    go (Quote a) = unquote a

o :: Expr var (b -> c) -> Expr var (a -> b) -> Expr var (a -> c)
o g f = Lam (\x -> App g (App f (Var x)))
infixr 9 `o`

dimapMoore
  :: Expr var (a -> b)
  -> Expr var (c -> d)
  -> Expr var (Moore b c -> Moore a d)
dimapMoore f g =
  Fix $ \go ->
  Lam $ \m ->
    let
      m' = App UnMoore (Var m)
    in
      App Moore $
      Pair (App g $ App Fst m') (Var go `o` App Snd m' `o` f)

constM :: Expr var b -> Expr var (Moore a b)
constM x =
  Fix $ \val ->
  App Moore $
  Pair x (Lam $ \_ -> Var val)

data Grammar c e
  = MkGrammar
  { infer :: forall var. String -> Maybe (ESigma var c)
  , topLevel :: c e
  }

data Action var c where
  Subgoals :: [ESigma var c] -> Action var c
  Operator :: Operator var c -> Action var c
  Operand :: Action var c

mapAction :: (forall x. f x -> g x) -> Action var f -> Action var g
mapAction f (Subgoals a) =
  Subgoals $ (\(ESigma tm cat) -> ESigma tm (f cat)) <$> a
mapAction f (Operator (MkOperator a b g)) =
  Operator $ MkOperator (f a) (f b) g
mapAction _ Operand = Operand

class IsCategory c where
  is_ :: c a -> c b -> Maybe (Expr var (a -> b))
  result_ :: c a -> Exists c
  step_ :: ESigma var c -> Action var c

instance IsCategory c => IsCategory (Cat c) where
  is_ (Exact s) (Exact s')
    | s == s' = Just (Lam Var)
    | otherwise = Nothing
  is_ (Many a b) (Many a' b') =
    dimapMoore <$>
    is_ a' a <*>
    is_ b b'
  is_ a (Many _ b') =
    (\f -> Lam $ \x -> constM (App f $ Var x)) <$> is_ a b'
  is_ (Many _ b) a' =
    (\f -> Lam $ \m -> App f (App Fst (App UnMoore $ Var m))) <$> is_ b a'
  is_ (Union a b) c =
    (`o` Fst) <$> is_ a c <|> (`o` Snd) <$> is_ b c
  is_ a (Union b c) =
    (\f g -> Lam $ \a' -> Pair (App f $ Var a') (App g $ Var a')) <$>
    is_ a b <*>
    is_ a c
  is_ (Arrow a b) (Arrow a' b') =
    (\f g -> Lam $ \h -> g `o` Var h `o` f) <$>
    is_ a' a <*>
    is_ b b'
  is_ (C a) (C b) = is_ a b
  is_ _ _ = Nothing

  result_ (Union a b) =
    case result_ a of
      Exists a' ->
        case result_ b of
          Exists b' -> Exists (Union a' b')
  result_ (Arrow _ b) = result_ b
  result_ (Many _ b) = result_ b
  result_ (C e) =
    case result_ e of
      Exists e' -> Exists (C e')
  result_ a = Exists a

  step_ (ESigma tm cat) =
    case cat of
      Arrow a b -> Operator $ MkOperator a b tm
      Union a b -> Subgoals [ESigma (App Fst tm) a, ESigma (App Snd tm) b]
      Many a b ->
        let
          m' = App UnMoore tm
        in
          Subgoals [ESigma (Pair (App Fst m') (App Snd m')) (Union b (Arrow a cat))]
      C a ->
        mapAction C $ step_ (ESigma tm a)
      _ -> Operand

data Operator var c where
  MkOperator :: c a -> c b -> Expr var (a -> b) -> Operator var c

parse
  :: forall c e var
   . IsCategory c
  => Grammar c e -- ^ Grammar specification
  -> [String] -- ^ Input
  -> [Expr var e]
parse grammar b = parse' b Nothing []
  where
    parse'
      :: IsCategory c
      => [String] -- ^ Input
      -> Maybe (ESigma var c) -- ^ Current term
      -> [Operator var c] -- ^ Operator stack
      -> [Expr var e]
    parse' [] (Just (ESigma tm cat)) [] =
      case is_ cat (topLevel grammar) of
        Nothing -> []
        Just f -> [App f tm]
    parse' (i:input) Nothing operators =
      case infer grammar i of
        Nothing -> []
        Just v -> parse' input (Just v) operators
    parse' input (Just s@(ESigma tm cat)) operators =
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
                              Just h -> parse' input (Just $ ESigma (App f $ App h tm) out) operators'
    parse' [] Nothing _ = []
