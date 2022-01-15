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

𝕃 : (ℱ : List 𝕋 -> Set) -> (List 𝕋 -> Set)
𝕃 ℱ Γ = [ Γ ] + ℱ Γ × ℱ Γ + ℱ Γ
