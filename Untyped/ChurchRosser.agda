{-# OPTIONS --postfix-projections #-}

module Untyped.ChurchRosser where
open import Preliminaries
import Substitution
open Substitution ⊤
open import Untyped.Base

private variable
    n n' : List ⊤
    M N : Λ n

-- Develops an isotopic version of 𝓣, where certain lambdas are overlined.
data 𝓣̅ : (Γ : List ⊤) (uni-type : ⊤) -> Set where
    v : 𝓥 Γ ⋆ -> 𝓣̅ Γ ⋆
    ƛ_ : 𝓣̅ (Γ ◂ ⋆) ⋆ -> 𝓣̅ Γ ⋆
    ƛ̅_ : 𝓣̅ (Γ ◂ ⋆) ⋆ -> 𝓣̅ Γ ⋆
    _∙_ : 𝓣̅ Γ ⋆ -> 𝓣̅ Γ ⋆ -> 𝓣̅ Γ ⋆
infixr 10 ƛ_ ƛ̅_
Λ̅ : List ⊤ -> Set
Λ̅ Γ = 𝓣̅ Γ ⋆
private
    map' : ⦃ Weakening 𝒲 ⦄ -> [ 𝒲 => 𝓣̅ ] -> {Γ Δ : List ⊤} -> (𝓥 => 𝒲) Γ Δ -> (𝓣̅ => 𝓣̅) Γ Δ
    map' 𝔳 δ (v i) = 𝔳 (δ i)
    map' 𝔳 δ (ƛ t) = ƛ map' 𝔳 (δ ≪ _) t
    map' 𝔳 δ (ƛ̅ t) = ƛ̅ map' 𝔳 (δ ≪ _) t
    map' 𝔳 δ (t ∙ s) = (map' 𝔳 δ t) ∙ (map' 𝔳 δ s)
instance
    𝓣̅ˢ : Syntax 𝓣̅
    𝓣̅ˢ .var = v
    𝓣̅ˢ .map = map'

-- Naming convention: If both an unmarked and marked version
-- of a term appears, one is named M and the other is named M̅.
-- But when no ambiguity is present, I use M for both kinds.
variable
    M̅ N̅ : Λ̅ n

-- These two are related:
⌊_⌋ : Λ̅ n -> Λ n
⌊ v x ⌋ = v x
⌊ ƛ t ⌋ = ^ ⌊ t ⌋
⌊ ƛ̅ t ⌋ = ^ ⌊ t ⌋
⌊ t ∙ s ⌋ = ⌊ t ⌋ ∙ ⌊ s ⌋

⌈_⌉ : Λ n -> Λ̅ n
⌈ v x ⌉ = v x
⌈ ^ M ⌉ = ƛ ⌈ M ⌉
⌈ M ∙ N ⌉ = ⌈ M ⌉ ∙ ⌈ N ⌉

-- We relate these two:
⌊⌈_⌉⌋ : (M : Λ n) -> ⌊ ⌈ M ⌉ ⌋ ≡ M
⌊⌈ v x ⌉⌋ = refl
⌊⌈ ^ M ⌉⌋ rewrite ⌊⌈ M ⌉⌋ = refl
⌊⌈ M ∙ N ⌉⌋ rewrite ⌊⌈ M ⌉⌋ | ⌊⌈ N ⌉⌋ = refl


private  -- A reflection data structure
    infix 5 ⌊_⌋≡_
    data ⌊_⌋≡_ : Λ̅ n -> Λ n -> Set where
        v : ∀ {n} (i : 𝓥 n ⋆) -> ⌊ v i ⌋≡ v i
        ƛ_ : ⌊ M̅ ⌋≡ M -> ⌊ ƛ M̅ ⌋≡ ^ M
        ƛ̅_ : ⌊ M̅ ⌋≡ M -> ⌊ ƛ̅ M̅ ⌋≡ ^ M
        _∙_ : ⌊ M̅ ⌋≡ M -> ⌊ N̅ ⌋≡ N -> ⌊ M̅ ∙ N̅ ⌋≡ M ∙ N

    reflect : ∀ (M̅ : Λ̅ n) -> ⌊ M̅ ⌋≡ ⌊ M̅ ⌋
    reflect (v x) = v x
    reflect (ƛ M̅) = ƛ reflect M̅
    reflect (ƛ̅ M̅) = ƛ̅ reflect M̅
    reflect (M̅ ∙ N̅) = reflect M̅ ∙ reflect N̅

    view : ⌊ M̅ ⌋≡ M -> ⌊ M̅ ⌋ ≡ M
    view (v i) = refl
    view (ƛ r) rewrite view r = refl
    view (ƛ̅ r) rewrite view r = refl
    view (r ∙ s) rewrite view r | view s = refl

-- For every single step reduction, we can mark the redex:
mark : ∀ {M N : Λ n} -> M ⟶₁ N -> Λ̅ n
mark {M = (^ M) ∙ N} (red β) = (ƛ̅ ⌈ M ⌉) ∙ ⌈ N ⌉
mark {M = _ ∙ N} (appₗ r) = mark r ∙ ⌈ N ⌉
mark {M = N ∙ _} (appᵣ r) = ⌈ N ⌉ ∙ mark r
mark (lam r) = ƛ mark r

⌊mark_⌋ : (r : M ⟶₁ N) -> ⌊ mark r ⌋ ≡ M
⌊mark_⌋ {M = (^ M) ∙ N} (red β) rewrite ⌊⌈ M ⌉⌋ | ⌊⌈ N ⌉⌋ = refl
⌊mark_⌋ {M = _ ∙ M} (appₗ r) rewrite ⌊⌈ M ⌉⌋ | ⌊mark r ⌋ = refl
⌊mark_⌋ {M = M ∙ _} (appᵣ r) rewrite ⌊⌈ M ⌉⌋ | ⌊mark r ⌋ = refl
⌊mark_⌋ {M = ^ M} (lam r) rewrite ⌊mark r ⌋ = refl

-- We prove that the ⌊_⌋ function is a Hom:
private
    instance
        _ = Syntaxʷ ⦃ 𝓣̅ˢ ⦄
        _ = Syntaxʷ ⦃ 𝓣ˢ ⦄

    instance
        Hom⌊⌋ : Hom ⌊_⌋
        Hom⌊⌋ .Hvar = refl
        Hom⌊⌋ .Hwed = Hwed'
            where
                Hwed' : ⦃ _ : Weakening 𝒲 ⦄ (δ : [ 𝒲 => 𝓣̅ ])
                    -> ∀ {Γ Δ} (σ : (𝓥 => 𝒲) Γ Δ) {i} (t : 𝓣̅ Γ i)
                    -> ⌊ map δ σ t ⌋ ≡ map (⌊_⌋ ∘ δ) σ ⌊ t ⌋
                Hwed' δ σ (v x) = refl
                Hwed' δ σ (ƛ t) rewrite Hwed' δ (σ ≪ _) t = refl
                Hwed' δ σ (ƛ̅ t) rewrite Hwed' δ (σ ≪ _) t = refl
                Hwed' δ σ (t ∙ s)
                    rewrite Hwed' δ σ t | Hwed' δ σ s = refl
        Hom⌊⌋ .Hpol δ δ' nat wk = Hpol'
            where
                Hpol' : ∀ {Γ Δ} (σ : (𝓥 => 𝓣̅) Γ Δ) {i} (t : 𝓣̅ Γ i)
                    -> ⌊ map δ σ t ⌋ ≡ map δ' (⌊_⌋ ∘ σ) ⌊ t ⌋
                Hpol' σ (v x) = nat (σ x)
                Hpol' σ (ƛ t) = cong ^_ $
                    transp (cong (λ u -> ⌊ map δ (σ ≪ _) t ⌋ ≡ map δ' u ⌊ t ⌋) $
                        funext (wk σ)) $
                    Hpol' (σ ≪ _) t
                Hpol' σ (ƛ̅ t) = cong ^_ $
                    transp (cong (λ u -> ⌊ map δ (σ ≪ _) t ⌋ ≡ map δ' u ⌊ t ⌋) $
                        funext (wk σ)) $
                    Hpol' (σ ≪ _) t
                Hpol' σ (t ∙ s)
                    rewrite Hpol' σ t | Hpol' σ s = refl

-- We make a function that reduces all the marked redexes
φ : Λ̅ n -> Λ n
φ (v x) = v x
φ (ƛ r) = ^ φ r
φ (ƛ̅ r) = ^ φ r  -- This ƛ̅ is impossible, so actually writing anything here does the job
φ ((ƛ̅ r) ∙ s) = subst (𝕫/ φ s) (φ r)
φ (r ∙ s) = φ r ∙ φ s

-- On unmarked terms, it does nothing:
φ⌈_⌉ : (M : Λ n) -> φ ⌈ M ⌉ ≡ M
φ⌈ v x ⌉ = refl
φ⌈ ^ M ⌉ rewrite φ⌈ M ⌉ = refl
φ⌈ M ∙ N ⌉ with M | φ⌈ M ⌉
... | v x    | eq rewrite φ⌈ N ⌉ = refl
... | ^ M    | eq rewrite φ⌈ N ⌉ | eq = refl
... | M ∙ M' | eq rewrite φ⌈ N ⌉ | eq = refl

-- If you mark a term and reduce the marked redex, you get the result back:
φmark : (r : M ⟶₁ N) -> φ (mark r) ≡ N
φmark {M = (^ M) ∙ N}  (red β)  rewrite φ⌈ M ⌉ | φ⌈ N ⌉       = refl
φmark {M = v x ∙ N}    (appᵣ r) rewrite φmark r               = refl
φmark {M = (^ M) ∙ N}  (appᵣ r) rewrite φmark r | φ⌈ M ⌉      = refl
φmark {M = M ∙ M' ∙ N} (appᵣ r) rewrite φmark r | φ⌈ M ∙ M' ⌉ = refl
φmark {M = ^ M}        (lam r)  rewrite φmark r               = refl
φmark {M = M ∙ N} (appₗ r@(red β))
    rewrite φmark r | φ⌈ N ⌉ = refl
φmark {M = M ∙ N} (appₗ r@(appₗ _))
    rewrite φmark r | φ⌈ N ⌉ = refl
φmark {M = M ∙ N} (appₗ r@(appᵣ _))
    rewrite φmark r | φ⌈ N ⌉ = refl
φmark {M = M ∙ N} (appₗ r@(lam _))
    rewrite φmark r | φ⌈ N ⌉ = refl

-- φ really computes a genuine reduction:
φred : (M : Λ̅ n)
    -> ⌊ M ⌋ ⟶ φ M
φred (v x) = begin _
φred (ƛ M) = mapₜ lam_ (φred M)
φred (ƛ̅ M) = mapₜ lam_ (φred M)
φred ((v _) ∙ N)     = mapₜ appᵣ_ (φred N)
φred (M@(ƛ _) ∙ N)   = mapₜ appᵣ_ (φred N) ⁀ mapₜ appₗ_ (φred M)
φred (M@(_ ∙ _) ∙ N) = mapₜ appᵣ_ (φred N) ⁀ mapₜ appₗ_ (φred M)
φred ((ƛ̅ M) ∙ N)
    = mapₜ appᵣ_          (φred N)
    ⁀ mapₜ (appₗ_ ∘ lam_) (φred M)
    ⁀ begin _ to _ by red β

-- Now we set off to define a reduction relation on Λ̅
infix 2 _↝̅_ _⟶̅₁_ _⟶̅_
data _↝̅_ {n} : Λ̅ n -> Λ̅ n -> Set where
    β : ∀ {M : Λ̅ (n ⁺)} {N : Λ̅ n}
        -> (ƛ M) ∙ N ↝̅ subst (𝕫/ N) M
    β̅ : ∀ {M : Λ̅ (n ⁺)} {N : Λ̅ n}
        -> (ƛ̅ M) ∙ N ↝̅ subst (𝕫/ N) M
data _⟶̅₁_ {n} : Λ̅ n -> Λ̅ n -> Set where
    red_ : {M M' : Λ̅ n} -> M ↝̅ M' -> M ⟶̅₁ M'
    appₗ_ : {M M' N : Λ̅ n} -> M ⟶̅₁ M' -> M ∙ N ⟶̅₁ M' ∙ N
    appᵣ_ : {M N N' : Λ̅ n} -> N ⟶̅₁ N' -> M ∙ N ⟶̅₁ M ∙ N'
    lam_ : {M M' : Λ̅ (n ⁺)} -> M ⟶̅₁ M' -> ƛ M ⟶̅₁ ƛ M'
    l̅am_ : {M M' : Λ̅ (n ⁺)} -> M ⟶̅₁ M' -> ƛ̅ M ⟶̅₁ ƛ̅ M'
infixr 9 l̅am_
_⟶̅_ : Λ̅ n -> Λ̅ n -> Set
_⟶̅_ = Trans _⟶̅₁_

red₁⌊_⌋ : M̅ ⟶̅₁ N̅ -> ⌊ M̅ ⌋ ⟶₁ ⌊ N̅ ⌋
red₁⌊_⌋ {M̅ = (ƛ M̅) ∙ N̅} (red β)
    = transp  -- We cannot rewrite by (Hsubst𝕫/_ N̅ M̅) because ⊤ get eta-expanded
        (cong ((^ ⌊ M̅ ⌋) ∙ ⌊ N̅ ⌋ ⟶₁_) $
            symm $ Hsubst𝕫/_ N̅ M̅) $
        red β
red₁⌊_⌋ {M̅ = (ƛ̅ M̅) ∙ N̅} (red β̅)
    = transp
        (cong ((^ ⌊ M̅ ⌋) ∙ ⌊ N̅ ⌋ ⟶₁_) $
            symm $ Hsubst𝕫/_ N̅ M̅) $
        red β
red₁⌊ appₗ r ⌋ = appₗ red₁⌊ r ⌋
red₁⌊ appᵣ r ⌋ = appᵣ red₁⌊ r ⌋
red₁⌊ lam r ⌋ = lam red₁⌊ r ⌋
red₁⌊ l̅am r ⌋ = lam red₁⌊ r ⌋

red⌊_⌋ : M̅ ⟶̅ N̅ -> ⌊ M̅ ⌋ ⟶ ⌊ N̅ ⌋
red⌊_⌋ = mapₜ red₁⌊_⌋
