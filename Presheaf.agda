{-# OPTIONS --allow-unsolved-metas #-}

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
    Presheaf.mapₚ よ σ δ v = σ (δ v)
    Presheaf.compₚ よ σ δ = refl
    Presheaf.idₚ よ = refl

    Ι : Presheaf [_]
    Presheaf.mapₚ Ι σ (exists v) = exists (σ v)
    Presheaf.compₚ Ι σ δ = funext λ _ -> refl
    Presheaf.idₚ Ι = funext λ _ -> refl

record Hom ⦃ _ : Presheaf 𝒞 ⦄ ⦃ _ : Presheaf 𝒟 ⦄
    (𝔉 : ∀ {Γ} -> 𝒞 Γ -> 𝒟 Γ) : Set where
    field
        natural : (σ : Γ => Δ) -> 𝔉 ∘ mapₚ σ ≡ mapₚ σ ∘ 𝔉
open Hom ⦃...⦄

instance
    よₕ : {σ : Θ => Δ}
        -> Hom ⦃ よ ⦄ ⦃ よ ⦄ (_∘ σ)
    Hom.natural よₕ σ = refl

_⊕_ : (𝒞 𝒟 : List I -> Set) -> List I -> Set
(𝒞 ⊕ 𝒟) Γ = 𝒞 Γ + 𝒟 Γ

instance
    Psh⊕ : ⦃ Presheaf 𝒞 ⦄ -> ⦃ Presheaf 𝒟 ⦄ -> Presheaf (𝒞 ⊕ 𝒟)
    Presheaf.mapₚ Psh⊕ σ (ι₁ x) = ι₁ (mapₚ σ x)
    Presheaf.mapₚ Psh⊕ σ (ι₂ x) = ι₂ (mapₚ σ x)
    Presheaf.compₚ Psh⊕ σ δ = funext λ { (ι₁ x) -> cong (λ u -> ι₁ (u x)) (compₚ σ δ)
                                       ; (ι₂ x) -> cong (λ u -> ι₂ (u x)) (compₚ σ δ) }
    Presheaf.idₚ Psh⊕ = funext λ { (ι₁ x) -> cong (λ u -> ι₁ (u x)) idₚ
                                 ; (ι₂ x) -> cong (λ u -> ι₂ (u x)) idₚ }

_⊗_ : (𝒞 𝒟 : List I -> Set) -> List I -> Set
(𝒞 ⊗ 𝒟) Γ = 𝒞 Γ × 𝒟 Γ

instance
    Psh⊗ : ⦃ Presheaf 𝒞 ⦄ -> ⦃ Presheaf 𝒟 ⦄ -> Presheaf (𝒞 ⊗ 𝒟)
    Presheaf.mapₚ Psh⊗ σ ⟨ x , y ⟩ = ⟨ mapₚ σ x , mapₚ σ y ⟩
    Presheaf.compₚ Psh⊗ σ δ = funext {!   !}
    Presheaf.idₚ Psh⊗ = funext {!   !}

