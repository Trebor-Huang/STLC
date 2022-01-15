module PHOAS where

data 𝕋 : Set where
    ι : 𝕋
    _⇒_ : 𝕋 -> 𝕋 -> 𝕋
infixr 10 _⇒_

data Λ (+ - : Set) : Set where
    var : + -> Λ + -
    app : Λ + - -> Λ + - -> Λ + -
    lam : (- -> Λ + -) -> Λ + -

dimap : ∀ {+₁ +₂ -₁ -₂} -> (+₁ -> +₂) -> (-₂ -> -₁) -> Λ +₁ -₁ -> Λ +₂ -₂
dimap f g (var x) = var (f x)
dimap f g (app m n) = app (dimap f g m) (dimap f g n)
dimap f g (lam m) = lam λ v -> dimap f g (m (g v))

𝕃 : Set₁
𝕃 = ∀ v -> Λ v v

data _≡_ {ℓ} {A : Set ℓ} : A -> A -> Set ℓ where
    refl : ∀ {a} -> a ≡ a

id : ∀ {ℓ} {A : Set ℓ} -> A -> A
id a = a

