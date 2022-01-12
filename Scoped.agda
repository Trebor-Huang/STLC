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
        coh : ⦃ _ : Weakening 𝒲 ⦄
            -> (𝐹 : [ 𝒲 => 𝒞 ]) (ℑ : ⟦ 𝓥 => 𝒲 ==> 𝒲 => 𝒲 ⟧)
            -> (eq : ∀ {Γ Δ} (σ : (𝓥 => 𝒲) Γ Δ) {i : I} (t : 𝒲 Γ i)
                -> 𝐹 (ℑ σ t) ≡ mapᵥ 𝐹 σ (𝐹 t))
            -> ∀ {Γ Δ Θ} (σ : (𝓥 => 𝒲) Γ Δ) (θ : (𝓥 => 𝒲) Θ Γ) {i : I} (t : 𝒞 Θ i)
            -> mapᵥ 𝐹 σ (mapᵥ 𝐹 θ t) ≡ mapᵥ 𝐹 (ℑ σ ∘ θ) t

    𝕫/_ : 𝒞 Γ σ -> (𝓥 => 𝒞) (Γ ◂ σ) Γ
    (𝕫/ t) 𝕫 = t
    (𝕫/ t) (𝕤 i) = var i
    infixr 6 𝕫/_

    rename : ⟦ 𝓥 => 𝓥 ==> 𝒞 => 𝒞 ⟧
    rename = mapᵥ var

    rename-comp : (σ : (𝓥 => 𝓥) Γ Δ) (θ : (𝓥 => 𝓥) Θ Γ) {i : I} (t : 𝒞 Θ i)
        -> rename σ (rename θ t) ≡ rename (σ ∘ θ) t
    rename-comp σ θ t = coh var id {! cohᵥ σ θ t  !} σ θ t

    𝒞ʷ : Weakening 𝒞
    𝒞ʷ .weaken σ 𝕫 = var 𝕫
    𝒞ʷ .weaken σ (𝕤 i) = rename 𝕤_ (σ i)

    subst : ⟦ 𝓥 => 𝒞 ==> 𝒞 => 𝒞 ⟧
    subst = mapᵥ id
        where instance _ = 𝒞ʷ

    subst-comp : (σ : (𝓥 => 𝒞) Γ Δ) (θ : (𝓥 => 𝒞) Θ Γ) {i : I} (t : 𝒞 Θ i)
        -> subst σ (subst θ t) ≡ subst (subst σ ∘ θ) t
    subst-comp σ θ t = coh id subst (\ _ _ -> refl) σ θ t
        where instance _ = 𝒞ʷ

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
            -> (eq : ∀ Γ σ i -> f (δ {Γ = Γ} {σ = σ} i) ≡ δ' (f i))
            -> (wk : ∀ {Γ Δ} (σ : (𝓥 => 𝒞) Γ Δ) {τ τ'}
                -> f {σ = τ} ∘ (weaken {σ = τ'} σ) ≡ (f ∘ σ) ʷ)
            -> ∀ {Γ Δ} {σ : (𝓥 => 𝒞) Γ Δ} {τ} (i : 𝒞 Γ τ)
            -> f (mapᵥ δ σ i) ≡ (mapᵥ δ' (f ∘ σ)) (f i)

    private
        fH𝕫/_ : ∀ {Γ τ τ'} (t : 𝒞 Γ τ) (i : Γ ◂ τ ∋ τ')
            -> f ((𝕫/ t) i) ≡ (𝕫/ f t) i
        (fH𝕫/ t) 𝕫 = refl
        (fH𝕫/ t) (𝕤 i) = Hvar

    H𝕫/_ : ∀ {Γ τ} (t : 𝒞 Γ τ)
        -> (\{τ'} -> f {σ = τ'} ∘ (𝕫/ t)) ≡ (𝕫/ f t)
    H𝕫/ t =
        funext' \_ ->
        funext (fH𝕫/ t)

    private
        fHvar : (\{Γ σ} -> f {Γ = Γ} {σ = σ} ∘ var) ≡ var
        fHvar =
            funext' \ _ ->
            funext' \ _ ->
            funext  \ _ -> Hvar

    Hrename : ∀ {Γ Δ} (σ : (𝓥 => 𝓥) Γ Δ)
        -> ∀ {τ} (t : 𝒞 Γ τ)
        -> f (rename σ t) ≡ rename σ (f t)
    Hrename σ t rewrite symm fHvar = Hmapᵥ var t

    Hweaken : ∀ (σ : (𝓥 => 𝒞) Γ Δ) {τ τ'} (i : Γ ◂ τ' ∋ τ)
        -> f (weaken σ i) ≡ weaken (f ∘ σ) i
    Hweaken σ 𝕫 = Hvar
    Hweaken σ (𝕤 i) = Hrename 𝕤_ (σ i)

    private
        fHweaken : ∀ {Γ Δ} (σ : (𝓥 => 𝒞) Γ Δ) {t t' : I}
            -> f {σ = t} ∘ (weaken {σ = t'} σ) ≡ (f ∘ σ) ʷ
        fHweaken σ = funext (Hweaken σ)

    Hmap : (δ : [ 𝒞 => 𝒞 ]) (δ' : [ 𝒟 => 𝒟 ])
        -> (eq : ∀ Γ σ i -> f (δ {Γ = Γ} {σ = σ} i) ≡ δ' (f i))
        -> ∀ {Γ Δ} {σ : (𝓥 => 𝒞) Γ Δ} {τ} (i : 𝒞 Γ τ)
        -> f (mapᵥ δ σ i) ≡ (mapᵥ δ' (f ∘ σ)) (f i)
    Hmap δ δ' eq i = Hmap↕ δ δ' eq fHweaken i

    Hsubst : ∀ {Γ Δ} (σ : (𝓥 => 𝒞) Γ Δ)
        -> ∀ {τ} (t : 𝒞 Γ τ)
        -> f (subst σ t) ≡ subst (f ∘ σ) (f t)
    Hsubst σ t = Hmap id id (\ _ _ _ -> refl) t

    Hsubst𝕫/_ : ∀ {Γ τ τ'} (t : 𝒞 Γ τ) (t' : 𝒞 (Γ ◂ τ) τ')
        -> f (subst (𝕫/ t) t') ≡ subst (𝕫/ f t) (f t')
    Hsubst𝕫/_ t t' rewrite Hsubst (𝕫/ t) t' | H𝕫/ t = refl
open Hom ⦃...⦄
