{-# OPTIONS --postfix-projections #-}

open import Preliminaries
module Presheaf (I : Set) where

variable
    Î Î Î Î : List I  -- Contexts
    i j k l : I  -- Types
    ð ð : List I -> Set  -- Presheafs

infix 5 _â_
data _â_ : List I -> I -> Set where
    ð«  :          Î â i â i
    ð¤_ : Î â i -> Î â j â i
infixr 100 ð¤_

[_] : List I -> Set
[ Î ] = â[ i â I ] Î â i

infix 5 _=>_
_=>_ : List I -> List I -> Set
Î => Î = {i : I} -> Î â i -> Î â i

record Presheaf (â± : List I -> Set) : Setâ where
    field
        mapâ : (Ï : Î => Î) -> â± Î -> â± Î
        compâ : (Ï : Î => Î) (Î´ : Î => Î)
            -> mapâ (Ï â Î´) â¡ mapâ Ï â mapâ Î´
        idâ : mapâ (Î» {i} (v : Î â i) -> v) â¡ id
open Presheaf â¦...â¦

instance
    ã : Presheaf (Î =>_)
    ã .mapâ Ï Î´ v = Ï (Î´ v)
    ã .compâ Ï Î´ = refl
    ã .idâ = refl

    Î : Presheaf [_]
    Î .mapâ Ï (exists v) = exists (Ï v)
    Î .compâ Ï Î´ = funext Î» _ -> refl
    Î .idâ = funext Î» _ -> refl


record Hom â¦ _ : Presheaf ð â¦ â¦ _ : Presheaf ð â¦
    (ð : â {Î} -> ð Î -> ð Î) : Set where
    field
        natural : (Ï : Î => Î) -> ð â mapâ Ï â¡ mapâ Ï â ð
open Hom â¦...â¦

instance
    ãâ : {Ï : Î => Î}
        -> Hom â¦ ã â¦ â¦ ã â¦ (_â Ï)
    ãâ .natural Ï = refl

_â_ : (ð ð : List I -> Set) -> List I -> Set
(ð â ð) Î = ð Î + ð Î

instance
    Pshâ : â¦ Presheaf ð â¦ -> â¦ Presheaf ð â¦ -> Presheaf (ð â ð)
    Pshâ .mapâ Ï (Î¹â x) = Î¹â (mapâ Ï x)
    Pshâ .mapâ Ï (Î¹â x) = Î¹â (mapâ Ï x)
    Pshâ â¦ ðáµ â¦ â¦ ðáµ â¦ .compâ Ï Î´ = funext aux
        where
            aux : _
            aux (Î¹â x) rewrite compâ â¦ ðáµ â¦ Ï Î´ = refl
            aux (Î¹â x) rewrite compâ â¦ ðáµ â¦ Ï Î´ = refl
    Pshâ â¦ ðáµ â¦ â¦ ðáµ â¦ .idâ {Î} = funext aux
        where
            aux : _
            aux (Î¹â x) rewrite idâ â¦ ðáµ â¦ {Î} = refl
            aux (Î¹â x) rewrite idâ â¦ ðáµ â¦ {Î} = refl

_â_ : (ð ð : List I -> Set) -> List I -> Set
(ð â ð) Î = ð Î Ã ð Î

instance
    Pshâ : â¦ Presheaf ð â¦ -> â¦ Presheaf ð â¦ -> Presheaf (ð â ð)
    Pshâ .mapâ Ï â¨ c , d â© = â¨ mapâ Ï c , mapâ Ï d â©
    Pshâ â¦ ðáµ â¦ â¦ ðáµ â¦ .compâ Ï Î´ = funext aux
        where
            aux : _
            aux â¨ c , d â© rewrite
                  compâ â¦ ðáµ â¦ Ï Î´
                | compâ â¦ ðáµ â¦ Ï Î´ = refl
    Pshâ â¦ ðáµ â¦ â¦ ðáµ â¦ .idâ {Î} = funext aux
        where
            aux : _
            aux â¨ c , d â© rewrite
                  idâ â¦ ðáµ â¦ {Î}
                | idâ â¦ ðáµ â¦ {Î} = refl
