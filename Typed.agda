{-# OPTIONS --postfix-projections #-}

module Typed where
open import Preliminaries

data 𝕋 : Set where
    ι : 𝕋
    _⇒_ : 𝕋 -> 𝕋 -> 𝕋

import Presheaf as Psh
open Psh 𝕋

open Presheaf ⦃...⦄
open Hom ⦃...⦄
instance
    𝕃 : ⦃ Presheaf 𝒞 ⦄ -> Presheaf ([_] ⊕ (𝒞 ⊗ 𝒞))
    𝕃 = {!   !}
