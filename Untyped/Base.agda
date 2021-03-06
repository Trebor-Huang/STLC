{-# OPTIONS --postfix-projections #-}

module Untyped.Base where
open import Preliminaries
import Substitution
open Substitution β€

-- Untyped is unityped
data π£ : (Ξ : List β€) (uni-type : β€) -> Set where
    v : π₯ Ξ β -> π£ Ξ β
    ^_ : π£ (Ξ β β) β -> π£ Ξ β
    _β_ : π£ Ξ β -> π£ Ξ β -> π£ Ξ β

infixl 20 _β_
infixr 10 ^_

pattern _βΊ Ξ = Ξ β β
infixl 30 _βΊ

-- A synonym to avoid writing the boring type.
Ξ : List β€ -> Set
Ξ Ξ = π£ Ξ β

-- Common combinators
π : Ξ β
π = ^ v π«
π : Ξ β
π = ^ ^ v (π€ π«)
ππ : Ξ β
ππ = ^ ^ v π«
π : Ξ β
π = ^ ^ ^ (v (π€ π«) β v π«) β (v (π€ π€ π«) β v π«)

Ο : Ξ β
Ο = ^ v π« β v π«
Ξ© : Ξ β
Ξ© = Ο β Ο

-- Defines a Syntax instance so we can seamlessly manipulate syntax with binding
private
    π£Λ’map : β¦ Weakening π² β¦
        -> [ π² => π£ ]
        -> β¦ π₯ => π² ==> π£ => π£ β§
    π£Λ’map π Ο (v x) = π (Ο x)
    π£Λ’map π Ο (^ t) = ^ π£Λ’map π (Ο βͺ _) t
    π£Λ’map π Ο (t β s) = π£Λ’map π Ο t β π£Λ’map π Ο s
instance
    π£Λ’ : Syntax π£
    π£Λ’ .var = v
    π£Λ’ .map = π£Λ’map

private variable
    n : List β€

-- Defines the reduction relation.
infix 2 _β_ _βΆβ_ _βΆ_
-- Direct reduction:
data _β_ {n} : Ξ n -> Ξ n -> Set where
    Ξ² : β {M : Ξ (n βΊ)} {N : Ξ n}
        -> (^ M) β N β subst (π«/ N) M

-- Congruence closure:
data _βΆβ_ {n} : Ξ n -> Ξ n -> Set where
    red_ : {M M' : Ξ n} -> M β M' -> M βΆβ M'
    appβ_ : {M M' N : Ξ n} -> M βΆβ M' -> M β N βΆβ M' β N
    appα΅£_ : {M N N' : Ξ n} -> N βΆβ N' -> M β N βΆβ M β N'
    lam_ : {M M' : Ξ (n βΊ)} -> M βΆβ M' -> ^ M βΆβ ^ M'
infixr 9 red_ appβ_ appα΅£_ lam_

-- Transitive closure:
_βΆ_ : Ξ n -> Ξ n -> Set
_βΆ_ = Trans _βΆβ_

KIIβΆI : π β π β π βΆ π
KIIβΆI =
    begin π β π β π
    to ππ β π by appβ red Ξ²
    to π by red Ξ²

Ξ©βΆΞ© : Ξ© βΆ Ξ©
Ξ©βΆΞ© = begin Ξ© to Ξ© by red Ξ²

-- Strong normalization:
data SN {n} : Ξ n -> Set where
    ~> : β {M} -> (β {N} -> M βΆβ N -> SN N) -> SN M

-- Example strong normalization
SNI : SN π
SNI = ~> Ξ» { (lam red ()) }

-- They just pursue down every track of reduction
SNKI : SN (π β π)
SNKI = ~> Ξ» { (red Ξ²) -> ~> Ξ» { (lam lam red ()) }
            ; (appβ lam lam red ())
            ; (appα΅£ lam red ()) }

-- Some terms are not strongly normalizing
Β¬SNΞ© : SN Ξ© -> β₯
Β¬SNΞ© (~> r) = Β¬SNΞ© (r (red Ξ²))
