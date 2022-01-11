{-# OPTIONS --safe --without-K #-}

module Typed where
open import Preliminaries
open import Scoped

data 𝕋 : Set where
    ι : 𝕋
    _⇒_ : 𝕋 -> 𝕋 -> 𝕋
infixr 10 _⇒_

infix 5 _⊢_
data _⊢_ : 𝕋 -scoped where
    var' : Γ ∋ σ -> Γ ⊢ σ
    lam : Γ ◂ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
    app : Γ ⊢ σ ⇒ τ -> Γ ⊢ σ -> Γ ⊢ τ
𝓣 = _⊢_

private
    𝓣map : ⦃ Weakening 𝒲 ⦄ -> [ 𝒲 => 𝓣 ] -> {Γ Δ : List 𝕋} -> (𝓥 => 𝒲) Γ Δ -> (𝓣 => 𝓣) Γ Δ
    𝓣map 𝔳 δ (var' x) = 𝔳 (δ x)
    𝓣map 𝔳 δ (lam t) = lam (𝓣map 𝔳 (δ ʷ) t)
    𝓣map 𝔳 δ (app t s) = app (𝓣map 𝔳 δ t) (𝓣map 𝔳 δ s)

instance
    𝓣ˢ : Stable 𝓣
    𝓣ˢ .var = var'
    𝓣ˢ .vmap = 𝓣map
