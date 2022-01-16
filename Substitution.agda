{-# OPTIONS --postfix-projections #-}
module Substitution (I : Set) where
open import Preliminaries
open import Agda.Primitive

Scope = (Γ : List I) (i : I) -> Set  -- Indexed presheaf
Morph = (Γ Δ : List I) -> Set

variable
    Γ Δ Θ Ξ : List I
    i j k l : I
    𝒜 ℬ 𝒞 𝒟 𝒱 𝒲 : Scope

infix 5 _∋_
data _∋_ : Scope where
    𝕫  :          Γ ◂ i ∋ i
    𝕤_ : Γ ∋ i -> Γ ◂ j ∋ i
infixr 100 𝕤_

𝓥 = _∋_ -- alternative notation

private variable
    v w : 𝓥 Γ i

infix 4 _=>_
_=>_ : (𝒱 𝒞 : Scope) -> Morph
(𝒱 => 𝒞) Γ Δ = ∀ {i} -> 𝒱 Γ i -> 𝒞 Δ i

[_] : Morph -> Set
[ ℭ ] = ∀ {Γ} -> ℭ Γ Γ

infixr 3 _==>_
_==>_ : Morph -> Morph -> Morph
(ℭ ==> 𝔇) Γ Δ = ℭ Γ Δ -> 𝔇 Γ Δ

⟦_⟧ : Morph -> Set
⟦ ℭ ⟧ = ∀ {Γ Δ} -> ℭ Γ Δ

record Weakening (𝒞 : Scope) : Set where
    constructor pack-weaken
    field
        weaken : (𝓥 => 𝒞) Γ Δ -> ∀ iʷ -> (𝓥 => 𝒞) (Γ ◂ iʷ) (Δ ◂ iʷ)
open Weakening ⦃...⦄ public

infixl 50 _≪_
_≪_ : ⦃ Weakening 𝒞 ⦄
    -> ∀ {Γ Δ} -> (𝓥 => 𝒞) Γ Δ
    -> ∀ iʷ -> (𝓥 => 𝒞) (Γ ◂ iʷ) (Δ ◂ iʷ)
_≪_ = weaken

instance
    𝓥ʷ : Weakening 𝓥
    𝓥ʷ .weaken ρ i 𝕫 = 𝕫
    𝓥ʷ .weaken ρ i (𝕤 v) = 𝕤 (ρ v)

𝓥-compʷ : (σ : (𝓥 => 𝓥) Γ Δ) (τ : (𝓥 => 𝓥) Ξ Γ) (v : 𝓥 (Ξ ◂ i) j)
    -> ((σ ∘ τ) ≪ i) v ≡ (σ ≪ i) ((τ ≪ i) v)
𝓥-compʷ σ τ 𝕫 = refl
𝓥-compʷ σ τ (𝕤 v) = refl

record Syntax (𝒞 : Scope) : Set1 where
    field
        var : [ 𝓥 => 𝒞 ]  -- Natural transformation from var
        map : ⦃ Weakening 𝒲 ⦄
            -> [ 𝒲 => 𝒞 ]
            -> ⟦ 𝓥 => 𝒲 ==> 𝒞 => 𝒞 ⟧

    𝕫/_ : 𝒞 Γ i -> (𝓥 => 𝒞) (Γ ◂ i) Γ
    (𝕫/ t) 𝕫 = t
    (𝕫/ t) (𝕤 v) = var v
    infixr 6 𝕫/_

    rename : ⟦ 𝓥 => 𝓥 ==> 𝒞 => 𝒞 ⟧
    rename = map var

    Syntaxʷ : Weakening 𝒞
    Syntaxʷ .weaken σ i 𝕫 = var 𝕫
    Syntaxʷ .weaken σ i (𝕤 v) = rename 𝕤_ (σ v)

    subst : ⟦ 𝓥 => 𝒞 ==> 𝒞 => 𝒞 ⟧
    subst = map id
        where instance _ = Syntaxʷ
open Syntax ⦃...⦄ public

instance  -- Yoneda embedding
    𝓥ˢ : Syntax 𝓥
    𝓥ˢ .var = id
    𝓥ˢ .map 𝑓 σ v = 𝑓 (σ v)

-- A coherence theorem
𝓥ˢʷ : Syntaxʷ ⦃ 𝓥ˢ ⦄ ≡ 𝓥ʷ
𝓥ˢʷ = cong pack-weaken (
    funext' λ Γ ->
    funext' λ Δ ->
    funext  λ ρ ->
    funext  λ j ->
    funext' λ i ->
    funext  λ {  𝕫    -> refl
              ; (𝕤 v) -> refl })

-- record Stable (𝒞 : Scope) ⦃ 𝒞ˢ : Syntax 𝒞 ⦄ : Set₁ where
--     field
--         map-comp : ⦃ 𝒲ʷ : Weakening 𝒲 ⦄
--             -> ⦃ 𝒟ˢ : Syntax 𝒟 ⦄ 
--             -> (𝑔 : [ 𝒟 => 𝒞 ])
--             -> (𝑓 : [ 𝒲 => 𝒟 ])
--             -> ∀ {Γ Δ Θ}
--             -> (σ : (𝓥 => 𝒲) Γ Δ) (δ : (𝓥 => 𝒟) Θ Γ)
--             -> let instance _ = Syntaxʷ ⦃ 𝒟ˢ ⦄ in 
--             ∀ {i} (t : 𝒞 Θ i)
--                 -> map (𝑔 ∘ 𝑓) σ (map 𝑔 δ t) ≡ map 𝑔 (map 𝑓 σ ∘ δ) t

record Hom ⦃ 𝒞ˢ : Syntax 𝒞 ⦄ ⦃ 𝒟ˢ : Syntax 𝒟 ⦄
    (𝑓 : [ 𝒞 => 𝒟 ]) : Set₁ where
    private instance
        _ = Syntaxʷ ⦃ 𝒞ˢ ⦄
        _ = Syntaxʷ ⦃ 𝒟ˢ ⦄
    field
        Hvar : 𝑓 {Γ} {i} (var v) ≡ var v
        Hwed : ⦃ 𝒲ᶜ : Weakening 𝒲 ⦄ (δ : [ 𝒲 => 𝒞 ])
            -> ∀ {Γ Δ} (σ : (𝓥 => 𝒲) Γ Δ) {i} (v : 𝒞 Γ i)
            -> 𝑓 (map δ σ v) ≡ (map (𝑓 ∘ δ) σ) (𝑓 v)
        Hpol : (δ : [ 𝒞 => 𝒞 ]) (δ' : [ 𝒟 => 𝒟 ])
            -> (nat : ∀ {Γ σ} (t : 𝒞 Γ σ)
                -> 𝑓 (δ t) ≡ δ' (𝑓 t))
            -> (wk : ∀ {Γ Δ} (σ : (𝓥 => 𝒞) Γ Δ) {i j} (v : 𝓥 _ i)
                -> 𝑓 ((σ ≪ j) v) ≡ ((𝑓 ∘ σ) ≪ j) v)
            -> ∀ {Γ Δ} (σ : (𝓥 => 𝒞) Γ Δ) {i} (t : 𝒞 Γ i)
            -> 𝑓 (map δ σ t) ≡ map δ' (𝑓 ∘ σ) (𝑓 t)

    private
        fH𝕫/_ : (t : 𝒞 Γ i) (v : 𝓥 (Γ ◂ i) j)
            -> 𝑓 ((𝕫/ t) v) ≡ (𝕫/ 𝑓 t) v
        (fH𝕫/ t) 𝕫 = refl
        (fH𝕫/ t) (𝕤 v) = Hvar

    H𝕫/_ : ∀ (t : 𝒞 Γ i)
        -> (λ {j} -> 𝑓 {i = j} ∘ (𝕫/ t)) ≡ 𝕫/ 𝑓 t
    H𝕫/ t = funext' \ _ -> funext (fH𝕫/ t)

    private
        fHvar : (\{Γ i} -> 𝑓 {Γ} {i} ∘ var) ≡ var
        fHvar =
            funext' \ _ ->
            funext' \ _ ->
            funext  \ _ -> Hvar

    Hrename : ∀ {Γ Δ} (ρ : (𝓥 => 𝓥) Γ Δ)
        -> ∀ {i} (t : 𝒞 Γ i)
        -> 𝑓 (rename ρ t) ≡ rename ρ (𝑓 t)
    Hrename ρ t rewrite symm fHvar = Hwed var ρ t


    Hweaken : ∀ (σ : (𝓥 => 𝒞) Γ Δ) {i j} (v : Γ ◂ i ∋ j)
        -> 𝑓 ((σ ≪ i) v) ≡ ((𝑓 ∘ σ) ≪ i) v
    Hweaken σ 𝕫 = Hvar
    Hweaken σ (𝕤 v) = Hrename 𝕤_ (σ v)

    private
        fHweaken : (σ : (𝓥 => 𝒞) Γ Δ)
            -> 𝑓 {i = j} ∘ (σ ≪ i) ≡ (𝑓 ∘ σ) ≪ i
        fHweaken σ = funext (Hweaken σ)

    Hmap : (δ : [ 𝒞 => 𝒞 ]) (δ' : [ 𝒟 => 𝒟 ])
        -> (nat : ∀ {Γ σ} (t : 𝒞 Γ σ)
            -> 𝑓 (δ t) ≡ δ' (𝑓 t))
        -> ∀ {Γ Δ} (σ : (𝓥 => 𝒞) Γ Δ) {i} (t : 𝒞 Γ i)
        -> 𝑓 (map δ σ t) ≡ map δ' (𝑓 ∘ σ) (𝑓 t)
    Hmap δ δ' nat = Hpol δ δ' nat (λ σ v -> Hweaken σ v)

    Hsubst : ∀ {Γ Δ} (σ : (𝓥 => 𝒞) Γ Δ)
        -> ∀ {i} (t : 𝒞 Γ i)
        -> 𝑓 (subst σ t) ≡ subst (𝑓 ∘ σ) (𝑓 t)
    Hsubst σ t = Hmap id id (λ _ -> refl) σ t

    Hsubst𝕫/_ : ∀ {Γ i j} (t : 𝒞 Γ i) (t' : 𝒞 (Γ ◂ i) j)
        -> 𝑓 (subst (𝕫/ t) t') ≡ subst (𝕫/ 𝑓 t) (𝑓 t')
    Hsubst𝕫/_ t t' rewrite Hsubst (𝕫/ t) t' | H𝕫/ t = refl
open Hom ⦃...⦄ public
