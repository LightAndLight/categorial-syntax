module Syntax

%default total

data Category : Type where
  Expression : Category
  Atom : Category
  Ident : Category
  Empty : Category
  Exact : String -> Category

  Var : String -> Category
  Union : Category -> Category -> Category
  -- Mu : String -> Category -> Category
  Many : Category -> Category -> Category -> Category
  Arrow : Category -> Category -> Category

-- Many Y Z
-- Z | Y -> Z | Y -> Y -> Z | Y -> ...
-- Z | Y -> (Z | Y -> Z | ...)
--
-- Many Y Z ~ mu x. Z | Y -> x
--
-- semantics(Many Y Z) = List semantics(Y)
--
-- Many X Y Z
-- X | Y -> Z | Y -> Y -> Z | Y -> ...
-- X | Y -> (Z | Y -> Z | ...)
--
-- Many Y Z ~ X | (mu x. Z | Y -> x)
--
-- semantics(Many X Y Z) = List semantics(Y)

bases : Category -> List Category
bases (Union a b) = bases a ++ bases b
bases a = [a]

rename : String -> String -> Category -> Category
rename s s' (Var x) = if s == x then Var s' else Var x
rename s s' (Union a b) = Union (rename s s' a) (rename s s' b)
-- rename s s' (Mu x e) = if s == x then Mu x e else Mu x (rename s s' e)
rename s s' (Many a b c) = Many (rename s s' a) (rename s s' b) (rename s s' c)
rename s s' (Arrow a b) = Arrow (rename s s' a) (rename s s' b)
rename s s' a = a

subst : String -> Category -> Category -> Category
subst s e (Var x) = if s == x then e else Var x
subst s e (Union a b) = Union (subst s e a) (subst s e b)
-- subst s e (Mu x e') = if s == x then Mu x e' else Mu x (subst s e e')
subst s e (Many a b c) = Many (subst s e a) (subst s e b) (subst s e c)
subst s e (Arrow a b) = Arrow (subst s e a) (subst s e b)
subst _ _ a = a

cat_eq : Category -> Category -> Bool
cat_eq = go []
  where
    go : List (String, String) -> Category -> Category -> Bool
    go scope Expression Expression = True
    go scope Atom Atom = True
    go scope (Exact s) (Exact s') = s == s'
    go scope Empty Empty = True
    go scope (Var s) (Var s') =
      case lookup s scope of
        Nothing => False
        Just s'' => s' == s''
    go scope (Union a b) (Union a' b') =
      let bs = bases a' ++ bases b' in
      all (\b => any (assert_total (go scope b)) bs) (bases a ++ bases b)
    -- go scope (Mu x e) (Mu x' e') = go ((x, x') :: scope) e e'
    go scope (Many a b c) (Many a' b' c') =
      go scope a a' && go scope b b' && go scope c c'
    go scope (Arrow a b) (Arrow a' b') = go scope a a' && go scope b b'
    go scope Ident Ident = True
    go scope _ _ = False

{-
tm1 : Category
tm1 = Mu "x" (Arrow Atom (Union Expression (Var "x")))

tm2 : Category
tm2 = Mu "y" (Arrow Atom (Union Expression (Var "y")))

tm3 : Category
tm3 = Mu "y" (Arrow Atom (Union Expression (Var "x")))

test1 : cat_eq Syntax.tm1 Syntax.tm2 = True
test1 = Refl

test2 : Not (cat_eq Syntax.tm1 Syntax.tm3 = True)
test2 Refl impossible
-}

record Grammar where
  constructor MkGrammar
  infer : String -> Category
  topLevel : Category

lc : Grammar
lc = MkGrammar infer' Expression
where
  infer' : String -> Category
  infer' ds =
    if isCons (unpack ds) && all isDigit (unpack ds)
    then
    -- (Mu "x" (Arrow Expression (Union Expression (Var "x"))))
      Many Atom Atom Expression
    else
    if isCons (unpack ds) && all isAlpha (unpack ds)
    then
    -- (Mu "x" (Arrow Expression (Union Expression (Var "x"))))
      Many Ident Atom Expression
    else
      case ds of
        "\\" => Arrow Ident (Arrow (Exact ".") (Arrow Expression Expression))
        "(" =>
          Arrow
            Expression
            (Arrow
              (Exact ")")
              (Many
                 Atom
                 Atom
                 Expression))
                -- (Mu "x" (Arrow Atom (Union Expression (Var "x"))))))
        _ => Exact ds

is : Category -> Category -> Bool
is = go []
  where
    go : List (Category, Category) -> Category -> Category -> Bool
    go trail a b =
      assert_total $
      any (\(x, y) => cat_eq a x && cat_eq b y) trail ||
      case (a, b) of
        (Expression, Expression) => True
        (Atom, Atom) => True
        (Atom, Expression) => True
        (Ident, Ident) => True
        (Ident, Atom) => True
        (Ident, Expression) => True
        (Exact s, Exact s') => s == s'
        (Var x, Var x') => x == x'
        (Union x y, Union _ _) =>
          assert_total $
          any (\z => go trail z b) (bases x ++ bases y)
        (Empty, Union _ _) => True
        (a, Union b c) =>
          assert_total $ any (go trail a) (bases b ++ bases c)
        (Arrow x y, Arrow x' y') =>
          go trail (assert_smaller a x') (assert_smaller b x) &&
          go trail (assert_smaller a y) (assert_smaller b y')
        -- (Mu t a', b) => go ((a, b) :: trail) (assert_smaller a a') b
        -- (a, Mu t b') => go ((a, b) :: trail) a (assert_smaller b b')
        (Many x y z, Many x' y' z') =>
          is x x' &&
          is y' y &&
          is z z'
        (Arrow y z, Many x' y' z') =>
          is y' y &&
          is z z'
        (Many x y z, Arrow y' z') =>
          is y' y &&
          is z z'
        (a, Many a' _ _) => is a a'
        (Many a _ _, a') => is a a'
        (_, _) => False

is_test_1 : is Atom Atom = True
is_test_1 = Refl

-- is_test_2 : is (Mu "x" Atom) (Mu "y" Atom) = True
-- is_test_2 = Refl

is_test_3 : is (Arrow Expression Atom) (Arrow Atom Expression) = True
is_test_3 = Refl

-- is_test_4 :
  -- is (Mu "x" (Union Atom (Var "x"))) (Mu "y" (Union Atom (Var "y"))) = True
-- is_test_4 = Refl

-- is_test_5 : is Atom (Mu "y" (Union Atom (Var "y"))) = True
-- is_test_5 = Refl

-- is_test_6 : is Atom (Mu "y" (Union Atom (Arrow Atom $ Var "y"))) = True
-- is_test_6 = Refl

-- is_test_7 : is (Exact "boo") (Mu "y" (Union Atom (Arrow Atom $ Var "y"))) = False
-- is_test_7 = Refl

-- is_test_8 :
  -- is (Exact "boo") (Mu "y" (Union (Exact "boo") (Arrow Atom $ Var "y"))) = True
-- is_test_8 = Refl

{-
is_test_9 :
  is
    (Atom `Arrow` Exact "boo")
    (Mu "y" (Union (Exact "boo") (Arrow Atom $ Var "y")))
  =
  True
is_test_9 = Refl
-}

is_test_10 :
  is
    (Atom `Arrow` Exact "boo")
    (Atom `Arrow` Exact "boo")
  =
  True
is_test_10 = Refl

isSentence : Grammar -> List String -> Bool
isSentence g = go (topLevel g) [] Nothing
  where
    go : Category -> List Category -> Maybe Category -> List String -> Bool
    go goal [] Nothing [] = True
    go goal [] Nothing (s :: ss) = go goal [infer g s] Nothing ss
    go goal [] (Just x) [] =
      assert_total $
      case x of
        Union a b => go goal [] (Just a) [] || go goal [] (Just b) []
        _ => x `is` goal
    go goal [] (Just x) (s :: ss) = False
    go goal (Union a b :: operators) operand ss =
      assert_total $
      go goal (a :: operators) operand ss ||
      go goal (b :: operators) operand ss
    -- go goal (s@(Mu t e) :: operators) operand ss =
      -- assert_total $
      -- go goal (subst t s e :: operators) operand ss
    go goal (Many a b c :: operators) operand ss =
      assert_total $
      go goal (Union a (Arrow b (Many c b c)) :: operators) operand ss
    go goal os@(Arrow a b :: operators) Nothing (s :: ss) =
      assert_total $
      go goal (infer g s :: os) Nothing ss
    go goal os@(Arrow a b :: operators) (Just op) ss =
      assert_total $
      case op of
        Union a b => go goal os (Just a) ss || go goal os (Just b) ss
        _ => is op a && go goal (b :: operators) Nothing ss
    go goal (a :: operators) (Just op) ss = False
    go goal (a :: operators) Nothing ss =
      assert_total $ go goal operators (Just a) ss

test_recog_1 : isSentence Syntax.lc ["a"] = True
test_recog_1 = Refl

test_recog_2 : isSentence Syntax.lc ["a", "a"] = True
test_recog_2 = Refl

test_recog_3 : isSentence Syntax.lc ["a", "a", "a"] = True
test_recog_3 = Refl

test_recog_4 : isSentence Syntax.lc ["~"] = False
test_recog_4 = Refl

test_recog_5 : isSentence Syntax.lc ["\\", "x", ".", "x"] = True
test_recog_5 = Refl

test_recog_6 : isSentence Syntax.lc ["\\", "x", ".", "+"] = False
test_recog_6 = Refl

test_recog_7 : isSentence Syntax.lc ["(", "x", ")"] = True
test_recog_7 = Refl

test_recog_8 : isSentence Syntax.lc ["(", "x", ")", "(", "x", ")"] = True
test_recog_8 = Refl

data Expr = Lam String Expr | App Expr Expr | V String | I Nat

data Tree = Branch String (List Tree)

toInt : List Char -> Maybe Nat
toInt [] = Nothing
toInt xs = go $ reverse xs
  where
    charNat : Char -> Maybe Nat
    charNat '0' = Just 0
    charNat '1' = Just 1
    charNat '2' = Just 2
    charNat '3' = Just 3
    charNat '4' = Just 4
    charNat '5' = Just 5
    charNat '6' = Just 6
    charNat '7' = Just 7
    charNat '8' = Just 8
    charNat '9' = Just 9
    charNat _ = Nothing

    go : List Char -> Maybe Nat
    go [] = Just 0
    go (x :: xs) = (+) <$> charNat x <*> map (10 *) (go xs)

test_toInt : toInt (unpack "123") = Just 123
test_toInt = Refl

decode : Tree -> Maybe Expr
decode (Branch "Lam" [Branch x [], e]) = Lam x <$> decode e
decode (Branch "App" [f, x]) = App <$> decode f <*> decode x
decode (Branch "V" [Branch s []]) = Just $ V s
decode (Branch "I" [Branch s []]) = I <$> toInt (unpack s)
decode _ = Nothing

{-
parse : Grammar -> List String -> Maybe Tree

Expression : Category
Atom : Category
Ident : Category
Empty : Category
Exact : String -> Category

Var : String -> Category
Union : Category -> Category -> Category
-- Mu : String -> Category -> Category
Many : Category -> Category -> Category -> Category
Arrow : Category -> Category -> Category

apply : (a : T) -> semantics(T)

input:  [ string : T ]    tree:  Maybe (T' ** semantics(T'))    goal:  A

input:  [ a : A ]    tree:  Nothing    goal:  A
semantics(A) : Tree
input:  [ ]    tree:  Just (A ** apply(a))    goal:  A
done

input:  [ a : A -> B, b : A ]    tree:  Nothing    goal:  B
semantics(A -> B) : semantics(A) -> semantics(B)

input:  [ b : A ]    tree:  Just(A -> B ** apply(a))    goal:  B
input:  [ ]          tree:  Just(B ** apply(a) apply(b))    goal:  B
done
-}

data Moore a b = MkMoore b (a -> Moore a b)

Functor (Moore a) where
  map f (MkMoore b g) = assert_total $ MkMoore (f b) (map f . g)

dimap : (a' -> a) -> (b -> b') -> Moore a b -> Moore a' b'
dimap f g (MkMoore x y) = assert_total $ MkMoore (g x) (dimap f g . y . f)

partial
constM : b -> Moore a b
constM x = MkMoore x (\_ => constM x)

takeM : List a -> Moore a b -> List b
takeM [] _ = []
takeM (a :: as) (MkMoore b m) = b :: takeM as (m a)

data Category' : Type -> Type where
  Expression' : Category' Expr
  Atom' : Category' Expr
  Ident' : Category' String
  Exact' : String -> Category' String
  Union' : Category' a -> Category' b -> Category' (a, b)
  Arrow' : Category' a -> Category' b -> Category' (a -> b)
  -- Many a b ~ b | a -> Many a b
  -- semantics(Many a b) = semantics(b | a -> Many a b)
  -- semantics(Many a b) = ( semantics(b), semantics(a -> Many a b) )
  -- semantics(Many a b) = ( semantics(b), semantics(a) -> semantics(Many a b) )
  Many' : Category' a -> Category' b -> Category' (Moore a b)

is' : (c : Category' a) -> (d : Category' b) -> Maybe (a -> b)
is' Expression' Expression' = Just id
is' Atom' Expression' = Just id
is' Atom' Atom' = Just id
is' Ident' Ident' = Just id
is' Ident' Atom' = Just V
is' Ident' Expression' = Just V
is' (Exact' s) (Exact' s') = if s == s' then Just id else Nothing
is' (Many' a b) (Many' a' b') =
  dimap <$>
  is' (assert_smaller (Many' a b) a') a <*>
  is' b b'
is' a (Many' a' b') = (\f, x => assert_total $ constM (f x)) <$> is' a b'
is' (Many' a b) a' = (\f, (MkMoore x _) => f x) <$> is' b a'
is' (Union' a b) c =
  (. fst) <$> is' a c <|> (. snd) <$> is' b c
is' a (Union' b c) =
  (\f, g, a => (f a, g a)) <$>
  is' a b <*>
  is' a c
is' (Arrow' a b) (Arrow' a' b') =
  -- couldn't do liftA2
  case is' (assert_smaller (Arrow' a b) a') a of
    Nothing => Nothing
    Just f =>
      case is' b b' of
        Nothing => Nothing
        Just g => Just $ \h => g . h . f
is' _ _ = Nothing

record Grammar' e where
  constructor MkGrammar'
  infer' : String -> Maybe (a : Type ** x : a ** Category' a)
  topLevel' : Category' e

parse : Grammar' e -> List String -> List e
parse g = go (topLevel' g) Nothing
  where
    go :
      Category' e ->
      Maybe (a : Type ** x : a ** Category' a) ->
      List String ->
      List e
    go goal Nothing [] = []
    go goal Nothing (x :: xs) =
      case infer' g x of
        Nothing => []
        Just tm => go goal (Just tm) xs
    go goal (Just (_ ** tm ** cat)) [] =
      case is' cat goal of
        Nothing => []
        Just f => [f tm]
    go goal (Just (_ ** tm ** cat)) (x :: xs) =
      case cat of
        Arrow' a b =>
          case infer' g x of
            Nothing => []
            Just (_ ** tm' ** Arrow' a' b') =>
              case is' b' a of
                Nothing => []
                Just f => go goal (Just (_ ** tm . f . tm' ** Arrow' a' b)) xs
            Just (_ ** tm' ** Many' a' b') =>
              case is' (Many' a' b') a of
                Nothing => []
                Just f =>
                  case tm' of
                    MkMoore v h =>
                      assert_total $
                      go goal (Just (_ ** tm (f (constM v)) ** b)) xs ++
                      go goal (Just (_ ** tm . f . h ** Arrow' a' b)) xs
            Just (_ ** tm' ** Union' a' b') =>
              assert_total $
              (case is' a' a of
                 Nothing => []
                 Just f => go goal (Just (_ ** tm (f $ fst tm') ** b)) xs) ++
              (case is' b' a of
                 Nothing => []
                 Just f => go goal (Just (_ ** tm (f $ snd tm') ** b)) xs)
            Just (_ ** tm' ** cat') =>
              case is' cat' a of
                Nothing => []
                Just f => go goal (Just (_ ** tm (f tm') ** b)) xs
        Union' a b =>
          assert_total $
          go goal (Just (_ ** fst tm ** a)) (x :: xs) ++
          go goal (Just (_ ** snd tm ** b)) (x :: xs)
        Many' a b =>
          case tm of
            MkMoore v f =>
              assert_total $
              go goal (Just (_ ** v ** b)) (x :: xs) ++
              go goal (Just (_ ** f ** Arrow' a (Many' a b))) (x :: xs)
        Exact' s => if x == s then go goal Nothing xs else []
        _ => []

foldlM : (b -> a -> b) -> b -> Moore a b
foldlM f a = assert_total $ MkMoore a $ foldlM f . f a

testGrammar : Grammar' Expr
testGrammar = MkGrammar' infer'' Expression'
  where
    infer'' : String -> Maybe (a : Type ** x : a ** Category' a)
    -- works
    -- infer'' a = Just (_ ** (V a, foldlM App (V a)) ** Union' Atom' (Many' Atom' Expression'))
    infer'' "(" = Just (_ ** \e, _ => e ** Arrow' Expression' (Arrow' (Exact' ")") Expression'))
    infer'' a =
      if all isAlpha (unpack a)
      then Just (_ ** V a ** Atom')
      else Just (_ ** a ** Exact' a)

lc' : Grammar' Expr
lc' = MkGrammar' infer'' Expression'
  where
    infer'' : String -> Maybe (a : Type ** x : a ** Category' a)
    infer'' cs =
      if all isDigit (unpack cs)
      then
        Just
          ( _ **
            let x = I (cast cs) in (the Expr x, foldlM App x) **
            Union' Atom' (Many' Atom' Expression')
          )
      else if all isAlpha (unpack cs)
      then
        Just
          ( _ **
            (cs, foldlM App (V cs)) **
            Union' Ident' (Many' Atom' Expression')
          )
      else case cs of
        "\\" =>
          Just
            ( _ **
              \x, _, e => Lam x e **
              Arrow' Ident' (Arrow' (Exact' ".") (Arrow' Expression' Expression'))
            )
        "(" =>
          Just
            ( _ **
              -- \e, _ => foldlM App e **
              \e, _ => e **
              Arrow'
                Expression'
                (Arrow'
                   (Exact' ")")
                   Expression')
                   -- (Many'
                      -- Atom'
                      -- Expression'))
            )
        _ => Just (_ ** cs ** Exact' cs)


{-
Path : Type
Path = List Nat

data Node : Type where
  Bot : Node
  Top : Node
  Arr : Node -> Node -> Node
  V : String -> Node

arity : Node -> Nat
arity Bot = 0
arity Top = 0
arity (Arr _ _) = 2
arity (V _) = 0

Tree : Type
Tree = Path -> Maybe Node

All : (a -> Type) -> List a -> Type
All p [] = ()
All p (x :: xs) = (p x, All p xs)

PrefixClosed : Tree -> Type
PrefixClosed t =
  (p : Path) ->
  IsJust (t p) ->
  All (IsJust . t) (inits p)

zeroToI : (i : Nat) -> List Nat
zeroToI Z = []
zeroToI (S n) = enumFromTo 0 n

Siblings : Tree -> Type
Siblings t =
  (p : Path) ->
  case t p of
    Nothing => ()
    Just l => All (\a => IsJust (t (p ++ [a]))) (zeroToI (arity l))

data Ty = TyVar String | TyBot | TyTop | TyArr Ty Ty | TyMu String Ty

substTy : String -> Ty -> Ty -> Ty
substTy s new (TyVar s') = if s == s' then new else TyVar s'
substTy s new (TyArr a b) = TyArr (substTy s new a) (substTy s new b)
substTy s new (TyMu n a) =
  if s == n
  then TyMu n a
  else TyMu n (substTy s new a)
substTy _ _ a = a

T : Ty -> Node
T TyBot = Bot
T TyTop = Top
T (TyVar a) = V a
T (TyArr a b) = Arr (T a) (T b)
T (TyMu t a) =
  if nestedMus t a
  then Bot
  else assert_total $ T (substTy t (TyMu t a) a)
  where
    nestedMus' : String -> Ty -> Bool
    nestedMus' t (TyMu t' a) = t /= t' && nestedMus' t a
    nestedMus' t (TyVar t') = t == t'
    nestedMus' _ _ = False

    nestedMus : String -> Ty -> Bool
    nestedMus t (TyMu t' a) = t /= t' && nestedMus' t a
    nestedMus _ _ = False

data Category' : Type -> Type where
  Expression' : Category' Expr
  Atom' : Category' Expr
  Ident' : Category' String
  Empty' : Category' Void
  Exact' : String -> Category' String

  Var' : String -> Category' String
  Union' : Category' a -> Category' b -> Category' (Either a b)
  Many' : Category' a -> Category' b -> Category' c -> Category' (List b -> c)
  Arrow' : Category' a -> Category' b -> Category' (a -> b)

record Grammar' a where
  constructor MkGrammar'
  infer' : String -> Maybe (t : Type ** x : t ** Category' t)
  topLevel' : Category' a

lc' : Grammar' Expr
lc' = MkGrammar' infer'' Expression'
  where
    infer'' : String -> Maybe (t : Type ** x : t ** Category' t)
    infer'' ds =
      if isCons (unpack ds) && all isDigit (unpack ds)
      then
        -- (Mu "x" (Arrow Expression (Union Expression (Var "x"))))
        Just (_ ** (foldl App (I $ cast ds)) ** Many' Atom' Atom' Expression')
      else
      if isCons (unpack ds) && all isAlpha (unpack ds)
      then
        -- (Mu "x" (Arrow Expression (Union Expression (Var "x"))))
        Just (_ ** (foldl App (V ds)) ** Many' Ident' Atom' Expression')
      else
        case ds of
        "\\" =>
          Just (_ **
           (\x, _, e => Lam x e) **
           Arrow' Ident' (Arrow' (Exact' ".") (Arrow' Expression' Expression')))
        "(" =>
          Just (_ **
           (\e, _ => foldl App e) **
           Arrow'
             Expression'
             (Arrow'
               (Exact' ")")
               (Many'
                 Atom'
                 Atom'
                 Expression')))
                -- (Mu "x" (Arrow Atom (Union Expression (Var "x"))))))
        _ => Nothing
   -}
