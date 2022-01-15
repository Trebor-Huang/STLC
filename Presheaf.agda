{-# OPTIONS --postfix-projections #-}

open import Preliminaries
module Presheaf (I : Set) where

variable
    Γ Δ Θ Ξ : List I  -- Contexts
    i j k l : I  -- Types
    𝒞 𝒟 : List I -> Set  -- Presheafs

infix 5 _∋_
data _∋_ : List I -> I -> Set where
    𝕫  :          Γ ◂ i ∋ i
    𝕤_ : Γ ∋ i -> Γ ◂ j ∋ i
infixr 100 𝕤_

[_] : List I -> Set
[ Γ ] = ∃[ i ∈ I ] Γ ∋ i

infix 5 _=>_
_=>_ : List I -> List I -> Set
Γ => Δ = {i : I} -> Γ ∋ i -> Δ ∋ i

record Presheaf (ℱ : List I -> Set) : Set₁ where
    field
        mapₚ : (σ : Γ => Δ) -> ℱ Γ -> ℱ Δ
        compₚ : (σ : Γ => Δ) (δ : Ξ => Γ)
            -> mapₚ (σ ∘ δ) ≡ mapₚ σ ∘ mapₚ δ
        idₚ : mapₚ (λ {i} (v : Γ ∋ i) -> v) ≡ id
open Presheaf ⦃...⦄

instance
    よ : Presheaf (Γ =>_)
    よ .mapₚ σ δ v = σ (δ v)
    よ .compₚ σ δ = refl
    よ .idₚ = refl

    Ι : Presheaf [_]
    Ι .mapₚ σ (exists v) = exists (σ v)
    Ι .compₚ σ δ = funext λ _ -> refl
    Ι .idₚ = funext λ _ -> refl


record Hom ⦃ _ : Presheaf 𝒞 ⦄ ⦃ _ : Presheaf 𝒟 ⦄
    (𝔉 : ∀ {Γ} -> 𝒞 Γ -> 𝒟 Γ) : Set where
    field
        natural : (σ : Γ => Δ) -> 𝔉 ∘ mapₚ σ ≡ mapₚ σ ∘ 𝔉
open Hom ⦃...⦄

instance
    よₕ : {σ : Θ => Δ}
        -> Hom ⦃ よ ⦄ ⦃ よ ⦄ (_∘ σ)
    よₕ .natural σ = refl

_⊕_ : (𝒞 𝒟 : List I -> Set) -> List I -> Set
(𝒞 ⊕ 𝒟) Γ = 𝒞 Γ + 𝒟 Γ

instance
    Psh⊕ : ⦃ Presheaf 𝒞 ⦄ -> ⦃ Presheaf 𝒟 ⦄ -> Presheaf (𝒞 ⊕ 𝒟)
    Psh⊕ .mapₚ σ (ι₁ x) = ι₁ (mapₚ σ x)
    Psh⊕ .mapₚ σ (ι₂ x) = ι₂ (mapₚ σ x)
    Psh⊕ ⦃ 𝒞ᵖ ⦄ ⦃ 𝒟ᵖ ⦄ .compₚ σ δ = funext aux
        where
            aux : _
            aux (ι₁ x) rewrite compₚ ⦃ 𝒞ᵖ ⦄ σ δ = refl
            aux (ι₂ x) rewrite compₚ ⦃ 𝒟ᵖ ⦄ σ δ = refl
    Psh⊕ ⦃ 𝒞ᵖ ⦄ ⦃ 𝒟ᵖ ⦄ .idₚ {Γ} = funext aux
        where
            aux : _
            aux (ι₁ x) rewrite idₚ ⦃ 𝒞ᵖ ⦄ {Γ} = refl
            aux (ι₂ x) rewrite idₚ ⦃ 𝒟ᵖ ⦄ {Γ} = refl

_⊗_ : (𝒞 𝒟 : List I -> Set) -> List I -> Set
(𝒞 ⊗ 𝒟) Γ = 𝒞 Γ × 𝒟 Γ

instance
    Psh⊗ : ⦃ Presheaf 𝒞 ⦄ -> ⦃ Presheaf 𝒟 ⦄ -> Presheaf (𝒞 ⊗ 𝒟)
    Psh⊗ .mapₚ σ ⟨ c , d ⟩ = ⟨ mapₚ σ c , mapₚ σ d ⟩
    Psh⊗ ⦃ 𝒞ᵖ ⦄ ⦃ 𝒟ᵖ ⦄ .compₚ σ δ = funext aux
        where
            aux : _
            aux ⟨ c , d ⟩ rewrite
                  compₚ ⦃ 𝒞ᵖ ⦄ σ δ
                | compₚ ⦃ 𝒟ᵖ ⦄ σ δ = refl
    Psh⊗ ⦃ 𝒞ᵖ ⦄ ⦃ 𝒟ᵖ ⦄ .idₚ {Γ} = funext aux
        where
            aux : _
            aux ⟨ c , d ⟩ rewrite
                  idₚ ⦃ 𝒞ᵖ ⦄ {Γ}
                | idₚ ⦃ 𝒟ᵖ ⦄ {Γ} = refl
