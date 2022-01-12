{-# OPTIONS --postfix-projections #-}
module Substitution (I : Set) where
open import Preliminaries
open import Agda.Primitive

Scope = (Γ : List I) (i : I) -> Set
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

infix 4 _=>_  -- Raw categories
_=>_ : (𝒱 𝒞 : Scope) -> (Γ Δ : List I) -> Set
(𝒱 => 𝒞) Γ Δ = ∀ {i} -> 𝒱 Γ i -> 𝒞 Δ i

[_] : Morph -> Set
[ ℭ ] = ∀ {Γ} -> ℭ Γ Γ

infix 3 _==>_
_==>_ : Morph -> Morph -> Morph
(ℭ ==> 𝔇) Γ Δ = ℭ Γ Δ -> 𝔇 Γ Δ

⟦_⟧ : Morph -> Set
⟦ ℭ ⟧ = ∀ {Γ Δ} -> ℭ Γ Δ

record Weakening (𝒞 : Scope) : Set where
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
        var : [ 𝓥 => 𝒞 ]
        mapᵥ : ⦃ Weakening 𝒲 ⦄
            -> [ 𝒲 => 𝒞 ]
            -> ⟦ 𝓥 => 𝒲 ==> 𝒞 => 𝒞 ⟧
        mapᵥ-var : (σ : (𝓥 => 𝓥) Γ Δ) (v : 𝓥 Γ i)
            -> mapᵥ var σ (var v) ≡ var (σ v)
        mapᵥ-comp : ⦃ _ : Weakening 𝒲 ⦄
            -> (𝑓 : [ 𝒲 => 𝒞 ]) (𝐹 : ⟦ 𝓥 => 𝒲 ==> 𝒲 => 𝒲 ⟧)
            -> (wk : ∀ {Γ Δ Ξ i j} (σ : (𝓥 => 𝒲) Γ Δ) (τ : (𝓥 => 𝒲) Ξ Γ) (t : 𝓥 (Ξ ◂ i) j)
                -> ((𝐹 σ ∘ τ) ≪ i) t ≡ 𝐹 (σ ≪ i) ((τ ≪ i) t))
            -> (eq : ∀ {Γ Δ i} (σ : (𝓥 => 𝒲) Γ Δ) (t : 𝒲 Γ i)
                -> mapᵥ 𝑓 σ (𝑓 t) ≡ 𝑓 (𝐹 σ t))
            -> ∀ {Γ Δ Ξ i} (σ : (𝓥 => 𝒲) Γ Δ) (τ : (𝓥 => 𝒲) Ξ Γ) (t : 𝒞 Ξ i)
                -> mapᵥ 𝑓 σ (mapᵥ 𝑓 τ t) ≡ mapᵥ 𝑓 (𝐹 σ ∘ τ) t
{-
    𝕫/_ : 𝒞 Γ i -> (𝓥 => 𝒞) (Γ ◂ i) Γ
    (𝕫/ t) 𝕫 = t
    (𝕫/ t) (𝕤 v) = var v
    infixr 6 𝕫/_

    rename : ⟦ 𝓥 => 𝓥 ==> 𝒞 => 𝒞 ⟧
    rename = mapᵥ var

    rename-comp : (σ : (𝓥 => 𝓥) Γ Δ) (θ : (𝓥 => 𝓥) Θ Γ) (t : 𝒞 Θ i)
        -> rename σ (rename θ t) ≡ rename (σ ∘ θ) t
    rename-comp = mapᵥ-comp var id 𝓥-compʷ mapᵥ-var

    Syntaxʷ : Weakening 𝒞
    Syntaxʷ .weaken σ i 𝕫 = var 𝕫
    Syntaxʷ .weaken σ i (𝕤 v) = rename 𝕤_ (σ v)
    private instance _ = Syntaxʷ

    subst : ⟦ 𝓥 => 𝒞 ==> 𝒞 => 𝒞 ⟧
    subst = mapᵥ id

    subst-compʷ : (σ : (𝓥 => 𝒞) Γ Δ) (τ : (𝓥 => 𝒞) Ξ Γ) (v : 𝓥 (Ξ ◂ i) j)
        -> ((subst σ ∘ τ) ≪ i) v ≡ subst (σ ≪ i) ((τ ≪ i) v)
    subst-compʷ {i = i} σ τ 𝕫 = {!   !}
    subst-compʷ σ τ (𝕤 v) = {!   !}

    subst-comp : (σ : (𝓥 => 𝒞) Γ Δ) (θ : (𝓥 => 𝒞) Θ Γ) (t : 𝒞 Θ i)
        -> subst σ (subst θ t) ≡ subst (subst σ ∘ θ) t
    subst-comp = mapᵥ-comp id subst subst-compʷ \ _ _ -> refl
open Syntax ⦃...⦄ public

record Hom (𝒞 𝒟 : Scope) ⦃ 𝒞ˢ : Syntax 𝒞 ⦄ ⦃ 𝒟ˢ : Syntax 𝒟 ⦄
    (f : [ 𝒞 => 𝒟 ]) : Set₁ where
    field
        Hvar : (v : 𝓥 Γ i) -> f (var v) ≡ var v
open Hom ⦃...⦄ public
-}