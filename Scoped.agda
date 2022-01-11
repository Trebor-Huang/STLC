{-# OPTIONS --safe --without-K --postfix-projections #-}

module Scoped where
open import Preliminaries
open import Agda.Primitive

_-scoped : (I : Set) -> Set1
I -scoped = (Γ : List I) (i : I) -> Set

variable
    I J A B : Set
    Γ Δ Θ : List I
    σ τ : I
    𝒞 𝒟 𝒱 𝒲 : I -scoped

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

infix 5 _⊚_
_⊚_ : [ 𝒞 => 𝒟 ] -> ∀ {Γ Δ} -> (𝒱 => 𝒞) Γ Δ -> (𝒱 => 𝒟) Γ Δ
(δ ⊚ σ) t = δ (σ t)

record Weakening (𝒞 : I -scoped) : Set where
    field
        weaken : (𝓥 => 𝒞) Γ Δ -> (𝓥 => 𝒞) (Γ ◂ σ) (Δ ◂ σ)
open Weakening ⦃...⦄ public

_ʷ : ⦃ Weakening 𝒞 ⦄ -> (𝓥 => 𝒞) Γ Δ -> (𝓥 => 𝒞) (Γ ◂ σ) (Δ ◂ σ)
_ʷ = weaken

Ren : (Γ Δ : List I) -> Set
Ren = 𝓥 => 𝓥

instance
    𝓥ʷ : Weakening (𝓥 {I = I})
    (𝓥ʷ .weaken) ρ 𝕫 = 𝕫
    (𝓥ʷ .weaken) ρ (𝕤 i) = 𝕤 ρ i

record Stable (𝒞 : I -scoped) : Set1 where
    private
        𝔖𝔢𝔪 : (𝒲 𝒟 : I -scoped) -> Set
        𝔖𝔢𝔪 𝒲 𝒟 = ∀ {Γ Δ} -> (𝓥 => 𝒲) Γ Δ -> (𝒞 => 𝒟) Γ Δ

    field
        var : [ 𝓥 => 𝒞 ]
        mapᵥ : ⦃ Weakening 𝒲 ⦄ -> [ 𝒲 => 𝒞 ] -> 𝔖𝔢𝔪 𝒲 𝒞

    rename : 𝔖𝔢𝔪 𝓥 𝒞
    rename = mapᵥ var

    𝒞ʷ : Weakening 𝒞
    𝒞ʷ .weaken σ 𝕫 = var 𝕫
    𝒞ʷ .weaken σ (𝕤 i) = rename 𝕤_ (σ i)

    subst : 𝔖𝔢𝔪 𝒞 𝒞
    subst = mapᵥ id
        where instance _ = 𝒞ʷ

    𝕫/_ : 𝒞 Γ σ -> (𝓥 => 𝒞) (Γ ◂ σ) Γ
    (𝕫/ t) 𝕫 = t
    (𝕫/ t) (𝕤 i) = var i
    infixr 6 𝕫/_

open Stable ⦃...⦄

