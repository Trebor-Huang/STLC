{-# OPTIONS --postfix-projections #-}

module PHOAS where
open import Preliminaries
open import Agda.Primitive

data 𝕋 : Set where
    ι : 𝕋
    _⇒_ : 𝕋 -> 𝕋 -> 𝕋
infixr 10 _⇒_

variable
    τ σ : 𝕋
    𝓥 : 𝕋 -> Set

data 𝓣 (𝓥 : 𝕋 -> Set) : 𝕋 -> Set where
    var : 𝓥 τ -> 𝓣 𝓥 τ
    app : 𝓣 𝓥 (τ ⇒ σ) -> 𝓣 𝓥 τ -> 𝓣 𝓥 σ
    lam : (𝓥 τ -> 𝓣 𝓥 σ) -> 𝓣 𝓥 (τ ⇒ σ)

subst : 𝓣 (𝓣 𝓥) τ -> 𝓣 𝓥 τ
subst (var t) = t
subst (app t s) = app (subst t) (subst s)
subst (lam x) = lam (subst ∘ x ∘ var)
