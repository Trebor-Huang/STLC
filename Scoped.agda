{-# OPTIONS --postfix-projections #-}
module Scoped where
open import Preliminaries
open import Agda.Primitive

_-scoped : (I : Set) -> Set1
I -scoped = (Γ : List I) (i : I) -> Set

variable
    I J A B : Set
    Γ Δ Θ : List I
    σ τ : I
    𝒜 ℬ 𝒞 𝒟 𝒱 𝒲 : I -scoped

infix 5 _∋_
data _∋_ {I} : I -scoped where
    𝕫  :          Γ ◂ σ ∋ σ
    𝕤_ : Γ ∋ σ -> Γ ◂ τ ∋ σ
infixr 100 𝕤_

𝓥 = _∋_ -- alternative notation
Fin = 𝓥 {I = ⊤}

infix 3 _=>_
_=>_ : (𝒱 𝒞 : I -scoped) -> (Γ Δ : List I) -> Set
(𝒱 => 𝒞) Γ Δ = ∀ {σ} -> 𝒱 Γ σ -> 𝒞 Δ σ

[_] : ((Γ Δ : List I) -> Set) -> Set
[ ℭ ] = ∀ {Γ} -> ℭ Γ Γ

⟦_==>_⟧ : ((Γ Δ : List I) -> Set) -> ((Γ Δ : List I) -> Set) -> Set
⟦ ℭ ==> 𝔇 ⟧ = ∀ {Γ Δ} -> ℭ Γ Δ -> 𝔇 Γ Δ

record Weakening (𝒞 : I -scoped) : Set where
    field
        weaken : (𝓥 => 𝒞) Γ Δ -> (𝓥 => 𝒞) (Γ ◂ σ) (Δ ◂ σ)
open Weakening ⦃...⦄ public

_ʷ : ⦃ Weakening 𝒞 ⦄ -> (𝓥 => 𝒞) Γ Δ -> (𝓥 => 𝒞) (Γ ◂ σ) (Δ ◂ σ)
_ʷ = weaken

instance
    𝓥ʷ : Weakening (𝓥 {I = I})
    (𝓥ʷ .weaken) ρ 𝕫 = 𝕫
    (𝓥ʷ .weaken) ρ (𝕤 i) = 𝕤 ρ i

record Stable (𝒞 : I -scoped) : Set1 where
    field
        var : [ 𝓥 => 𝒞 ]
        mapᵥ : ⦃ Weakening 𝒲 ⦄ -> [ 𝒲 => 𝒞 ]
            -> ⟦ 𝓥 => 𝒲 ==> 𝒞 => 𝒞 ⟧

    rename : ⟦ 𝓥 => 𝓥 ==> 𝒞 => 𝒞 ⟧
    rename = mapᵥ var

    𝒞ʷ : Weakening 𝒞
    𝒞ʷ .weaken σ 𝕫 = var 𝕫
    𝒞ʷ .weaken σ (𝕤 i) = rename 𝕤_ (σ i)

    subst : ⟦ 𝓥 => 𝒞 ==> 𝒞 => 𝒞 ⟧
    subst = mapᵥ id
        where instance _ = 𝒞ʷ

    𝕫/_ : 𝒞 Γ σ -> (𝓥 => 𝒞) (Γ ◂ σ) Γ
    (𝕫/ t) 𝕫 = t
    (𝕫/ t) (𝕤 i) = var i
    infixr 6 𝕫/_

open Stable ⦃...⦄

private instance
    _ : ⦃ Stable 𝒞 ⦄ -> Weakening 𝒞
    _ = 𝒞ʷ

record Hom (𝒞 𝒟 : I -scoped) ⦃ 𝒞ˢ : Stable 𝒞 ⦄ ⦃ 𝒟ˢ : Stable 𝒟 ⦄
    (f : [ 𝒞 => 𝒟 ]) : Set₁ where
    field
        Hvar : ∀ {Γ σ i} -> f {Γ = Γ} {σ = σ} (var i) ≡ var i
        Hmapᵥ : ⦃ 𝒲ᶜ : Weakening 𝒲 ⦄ (δ : [ 𝒲 => 𝒞 ])
            -> ∀ {Γ Δ} {σ : (𝓥 => 𝒲) Γ Δ} {τ} (i : 𝒞 Γ τ)
            -> f (mapᵥ δ σ i) ≡ (mapᵥ (f ∘ δ) σ) (f i)
        Hmap↕ : (δ : [ 𝒞 => 𝒞 ]) (δ' : [ 𝒟 => 𝒟 ])
            -> (∀ Γ σ i -> f (δ {Γ = Γ} {σ = σ} i) ≡ δ' (f i))
            -> ∀ {Γ Δ} {σ : (𝓥 => 𝒞) Γ Δ} {τ} (i : 𝒞 Γ τ)
            -> f (mapᵥ δ σ i)
                ≡ (mapᵥ δ' (f ∘ σ)) (f i)

    private
        fHvar : (\{Γ σ} -> f {Γ = Γ} {σ = σ} ∘ var) ≡ var
        fHvar =
            funext' \ _ ->
            funext' \ _ ->
            funext  \ _ -> Hvar

    Hrename : ∀ {Γ Δ} (σ : (𝓥 => 𝓥) Γ Δ)
        -> ∀ {τ} (t : 𝒞 Γ τ)
        -> f (rename σ t) ≡ rename σ (f t)
    Hrename {Γ = Γ} {Δ = Δ} σ {τ = τ} t
        rewrite symm fHvar = Hmapᵥ var t

    Hsubst : ∀ {Γ Δ} (σ : (𝓥 => 𝒞) Γ Δ)
        -> ∀ {τ} (t : 𝒞 Γ τ)
        -> f (subst σ t) ≡ subst (f ∘ σ) (f t)
    Hsubst σ t = Hmap↕ id id (\ _ _ _ -> refl) t

