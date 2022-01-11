module Untyped.Base where
open import Preliminaries
open import Scoped

-- Untyped is unityped
data 𝓣 : (Γ : List ⊤) (uni-type : ⊤) -> Set where
    v : 𝓥 Γ ⋆ -> 𝓣 Γ ⋆
    ^_ : 𝓣 (Γ ◂ ⋆) ⋆ -> 𝓣 Γ ⋆
    _∙_ : 𝓣 Γ ⋆ -> 𝓣 Γ ⋆ -> 𝓣 Γ ⋆

infixl 20 _∙_
infixr 10 ^_

pattern _⁺ Γ = Γ ◂ ⋆
infixl 30 _⁺

-- A synonym to avoid writing the boring type.
Λ : List ⊤ -> Set
Λ Γ = 𝓣 Γ ⋆

-- Common combinators
𝕀 : Λ ∅
𝕀 = ^ v 𝕫
𝕂 : Λ ∅
𝕂 = ^ ^ v (𝕤 𝕫)
𝕂𝕀 : Λ ∅
𝕂𝕀 = ^ ^ v 𝕫
𝕊 : Λ ∅
𝕊 = ^ ^ ^ (v (𝕤 𝕫) ∙ v 𝕫) ∙ (v (𝕤 𝕤 𝕫) ∙ v 𝕫)

ω : Λ ∅
ω = ^ v 𝕫 ∙ v 𝕫
Ω : Λ ∅
Ω = ω ∙ ω

-- Defines a Stable instance so we can seamlessly manipulate syntax with binding
private
    map : ⦃ Weakening 𝒲 ⦄ -> [ 𝒲 => 𝓣 ] -> {Γ Δ : List ⊤} -> (𝓥 => 𝒲) Γ Δ -> (𝓣 => 𝓣) Γ Δ
    map 𝔳 δ (v i) = 𝔳 (δ i)
    map 𝔳 δ (^ t) = ^ map 𝔳 (δ ʷ) t
    map 𝔳 δ (t ∙ s) = (map 𝔳 δ t) ∙ (map 𝔳 δ s)

instance
    𝓣ˢ : Stable 𝓣
    Stable.var 𝓣ˢ = v
    Stable.mapᵥ 𝓣ˢ = map

open Stable 𝓣ˢ

private variable
    n : List ⊤

-- Defines the reduction relation.
infix 2 _↝_ _⟶₁_ _⟶_
-- Direct reduction:
data _↝_ {n} : Λ n -> Λ n -> Set where
    β : ∀ {M : Λ (n ⁺)} {N : Λ n}
        -> (^ M) ∙ N ↝ subst (𝕫/ N) M

-- Congruence closure:
data _⟶₁_ {n} : Λ n -> Λ n -> Set where
    red_ : {M M' : Λ n} -> M ↝ M' -> M ⟶₁ M'
    appₗ_ : {M M' N : Λ n} -> M ⟶₁ M' -> M ∙ N ⟶₁ M' ∙ N
    appᵣ_ : {M N N' : Λ n} -> N ⟶₁ N' -> M ∙ N ⟶₁ M ∙ N'
    lam_ : {M M' : Λ (n ⁺)} -> M ⟶₁ M' -> ^ M ⟶₁ ^ M'
infixr 9 red_ appₗ_ appᵣ_ lam_

-- Transitive closure:
_⟶_ : Λ n -> Λ n -> Set
_⟶_ = Trans _⟶₁_

KII⟶I : 𝕂 ∙ 𝕀 ∙ 𝕀 ⟶ 𝕀
KII⟶I =
    begin 𝕂 ∙ 𝕀 ∙ 𝕀
    to 𝕂𝕀 ∙ 𝕀 by appₗ red β
    to 𝕀 by red β

Ω⟶Ω : Ω ⟶ Ω
Ω⟶Ω = begin Ω to Ω by red β

-- Strong normalization:
data SN {n} : Λ n -> Set where
    ~> : ∀ {M} -> (∀ {N} -> M ⟶₁ N -> SN N) -> SN M

-- Example strong normalization
SNI : SN 𝕀
SNI = ~> λ { (lam red ()) }

-- They just pursue down every track of reduction
SNKI : SN (𝕂 ∙ 𝕀)
SNKI = ~> λ { (red β) -> ~> λ { (lam lam red ()) }
            ; (appₗ lam lam red ())
            ; (appᵣ lam red ()) }

-- Some terms are not strongly normalizing
¬SNΩ : SN Ω -> ⊥
¬SNΩ (~> r) = ¬SNΩ (r (red β))

