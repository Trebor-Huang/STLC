module PHOAS where

data ð : Set where
    Î¹ : ð
    _â_ : ð -> ð -> ð
infixr 10 _â_

data Î (+ - : Set) : Set where
    var : + -> Î + -
    app : Î + - -> Î + - -> Î + -
    lam : (- -> Î + -) -> Î + -

dimap : â {+â +â -â -â} -> (+â -> +â) -> (-â -> -â) -> Î +â -â -> Î +â -â
dimap f g (var x) = var (f x)
dimap f g (app m n) = app (dimap f g m) (dimap f g n)
dimap f g (lam m) = lam Î» v -> dimap f g (m (g v))

ð : Setâ
ð = â v -> Î v v

data _â¡_ {â} {A : Set â} : A -> A -> Set â where
    refl : â {a} -> a â¡ a

id : â {â} {A : Set â} -> A -> A
id a = a

