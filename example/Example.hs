{-# language GADTs #-}
{-# language StandaloneDeriving #-}
module Main where

import Control.Moore
import Data.Char (isLetter, isDigit)
import Data.Exists
import Data.Sigma
import Language.Category

data SExp
  = Nil
  | Cons SExp SExp
  | Str String
  deriving (Eq, Show)

data SExpT a where
  AtomS :: SExpT SExp

instance IsCategory SExpT where
  is_ AtomS AtomS = Just id
  result_ AtomS = Exists AtomS
  step_ (Sigma _ AtomS) = Operand

sexp :: Grammar (Cat SExpT) SExp
sexp = MkGrammar infer (C AtomS)
  where
    infer :: String -> Maybe (Sigma (Cat SExpT))
    infer str
      | all isLetter str = Just $ Sigma (Str str) (C AtomS)
      | otherwise =
          case str of
            "(" ->
              Just $
              Sigma
                (foldrM (\a b s -> Cons a (b s)) (\_ -> Nil))
                (Many (C AtomS) (Exact ")" +> C AtomS))
            _ -> Just $ Sigma str (Exact str)

parseSexp :: String -> [SExp]
parseSexp = parse sexp . words

data Expr
  = Lam String Expr
  | App Expr Expr
  | V String
  | I Int
  deriving (Eq, Show)

data ExprT a where
  ExprE :: ExprT Expr
  AtomE :: ExprT Expr
  IdentE :: ExprT String
deriving instance Show (ExprT a)

instance IsCategory ExprT where
  is_ IdentE IdentE = Just id
  is_ IdentE AtomE = Just V
  is_ IdentE ExprE = Just V
  is_ AtomE AtomE = Just id
  is_ AtomE ExprE = Just id
  is_ ExprE ExprE = Just id
  is_ _ _ = Nothing

  result_ = Exists

  step_ = const Operand

lc :: Grammar (Cat ExprT) Expr
lc = MkGrammar infer (C ExprE)
  where
    infer :: String -> Maybe (Sigma (Cat ExprT))
    infer cs
      | all isDigit cs =
          Just $
            Sigma
              ( let val = I (read cs) in
                ( val
                , \e -> foldlM App (App val e)
                )
              )
              (C AtomE +| (C AtomE +> Many (C AtomE) (C ExprE))
      | all isLetter cs =
          Just $
            Sigma
              ( cs, \e -> foldlM App (App (V cs) e))
              (C IdentE +| (C AtomE +> Many (C AtomE) (C ExprE)))
      | otherwise =
          case cs of
            "\\" ->
              Just $
                Sigma
                  (\x _ e -> Lam x e)
                  (C IdentE +> Exact "." +> C ExprE +> C ExprE)
            "(" ->
              Just $
                Sigma
                  (\e _ -> (e, \e' -> foldlM App (App e e')))
                  (C ExprE +> Exact ")" +>
                   C AtomE +| (C AtomE +> Many (C AtomE) (C ExprE)))
            _ -> Just $ Sigma cs (Exact cs)

parseLc :: String -> [Expr]
parseLc = parse lc . words

main :: IO ()
main = do
  print $ parseLc "a 1"
  print $ parseLc "a \\ x . x"
  print $ parseLc "a b c"
  print $ parseLc "a ( b c d ) e"
  print . parseLc $
    "a b c d e f g h i j k l m n o p q r s t u v w x y z " ++
    "a b c d e f g h i j k l m n o p q r s t u v w x y z" ++
    "a b c d e f g h i j k l m n o p q r s t u v w x y z"
  print $ parseLc "\\ x . x"
  print $ parseSexp "( )"
  print $ parseSexp "( a b c )"
  print $ parseSexp "( a ( b c ) d )"
  print $ parseSexp "( a ( b c d )"
