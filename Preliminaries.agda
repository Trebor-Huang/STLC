module Preliminaries where
open import Agda.Primitive

-- Some preliminaries
data ℕ : Set where
    zero : ℕ
    succ : ℕ -> ℕ
{-# BUILTIN NATURAL ℕ #-}

data ⊥ : Set where
record ⊤ : Set where
    constructor ⋆

data _≡_ {ℓ} {A : Set ℓ} : A -> A -> Set ℓ where
    refl : ∀ {a} -> a ≡ a
{-# BUILTIN EQUALITY _≡_ #-}
infix 1 _≡_

cong : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}
    -> (f : A -> B) {a a' : A}
    -> a ≡ a' -> f a ≡ f a'
cong f refl = refl

symm : ∀ {ℓ} {A : Set ℓ} {a a' : A}
    -> a ≡ a' -> a' ≡ a
symm refl = refl

transp : ∀ {ℓ} {A B : Set ℓ}
    -> A ≡ B -> A -> B
transp refl a = a

data List {ℓ} (A : Set ℓ) : Set ℓ where
    ∅ : List A
    _◂_ : List A -> A -> List A
infixl 10 _◂_

data _×_ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
    ⟨_,_⟩ : A -> B -> A × B
infixl 1 _×_

data _+_ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
    ι₁ : A -> A + B
    ι₂ : B -> A + B
infixl 1 _+_

record Exists {ℓ ℓ'} (A : Set ℓ) (P : A -> Set ℓ') : Set (ℓ ⊔ ℓ') where
    constructor exists
    field
        {object} : A
        witness : P object
open Exists public
syntax Exists A (\x -> P) = ∃[ x ∈ A ] P
infixr 0 Exists

const : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}
    -> A -> B -> A
const a _ = a
{-# INLINE const #-}

id : ∀ {ℓ} {A : Set ℓ} -> A -> A
id a = a
{-# INLINE id #-}

infixl 3 _∘_
_∘_ : ∀ {ℓ ℓ' ℓ''}
    -> {A : Set ℓ} {B : Set ℓ'} {C : B -> Set ℓ''}
    -> (g : (b : B) -> C b) (f : A -> B)
    -> (a : A) -> C (f a)
(g ∘ f) x = g (f x)
{-# INLINE _∘_ #-}

infixr -1 _$_
_$_ : ∀ {ℓ ℓ'}
    -> {A : Set ℓ} {B : A -> Set ℓ'}
    -> (f : (a : A) -> B a) (a : A)
    -> B a
f $ a = f a
{-# INLINE _$_ #-}

-- Transitive closure
data Trans {ℓ ℓ'} {A : Set ℓ} (_~>_ : A -> A -> Set ℓ') : A -> A -> Set (ℓ ⊔ ℓ') where
    begin_ : (M : A) -> Trans _ M M
    _to_by_ : {M M' : A} -> Trans _~>_ M M' ->
        ∀ M'' -> (r : M' ~> M'') -> Trans _ M M''
infixl 3 _to_by_
infixr 4 begin_

-- Concatenation
_⁀_ : ∀ {ℓ ℓ'} {A : Set ℓ} {_~>_ : A -> A -> Set ℓ'} {M M' M'' : A}
    -> Trans _~>_ M M'
    -> Trans _~>_ M' M''
    -> Trans _~>_ M M''
R ⁀ (begin _) = R
R ⁀ (R' to _ by r) = (R ⁀ R') to _ by r

infixl 2 _⁀_

-- Mapping of transitive closures
mapₜ : ∀ {ℓ ℓ'} {A : Set ℓ} {_~>_ : A -> A -> Set ℓ'}
    -> ∀ {r r'} {B : Set r} {_⟶_ : B -> B -> Set r'}
    -> {f : A -> B} (F : ∀ {a a'} -> a ~> a' -> f a ⟶ f a')
    -> ∀ {a a'} -> Trans _~>_ a a' -> Trans _⟶_ (f a) (f a')
mapₜ F (begin _) = begin _
mapₜ F (R to _ by r) = mapₜ F R to _ by F r

postulate
    funext : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A -> Set ℓ'}
        -> {f g : (a : A) -> B a}
        -> (∀ a -> f a ≡ g a)
        -> f ≡ g

    funext' : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A -> Set ℓ'}
        -> {f g : {a : A} -> B a}
        -> (∀ a -> f {a} ≡ g {a})
        -> _≡_ {A = {a : A} -> B a} f g
    -- Fun challenge: These two can actually be reduced to one.
    -- Try proving that they are equivalent!

    -- The answers are located at
    -- https://ice1000.org/2021/03-02-AgdaEtaFunc.html
