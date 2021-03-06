{-# OPTIONS --postfix-projections #-}

module Untyped.ChurchRosser where
open import Preliminaries
import Substitution
open Substitution âĪ
open import Untyped.Base

private variable
    n n' : List âĪ
    M N : Î n

-- Develops an isotopic version of ðĢ, where certain lambdas are overlined.
data ðĢĖ : (Î : List âĪ) (uni-type : âĪ) -> Set where
    v : ðĨ Î â -> ðĢĖ Î â
    Æ_ : ðĢĖ (Î â â) â -> ðĢĖ Î â
    ÆĖ_ : ðĢĖ (Î â â) â -> ðĢĖ Î â
    _â_ : ðĢĖ Î â -> ðĢĖ Î â -> ðĢĖ Î â
infixr 10 Æ_ ÆĖ_
ÎĖ : List âĪ -> Set
ÎĖ Î = ðĢĖ Î â
private
    map' : âĶ Weakening ðē âĶ -> [ ðē => ðĢĖ ] -> {Î Î : List âĪ} -> (ðĨ => ðē) Î Î -> (ðĢĖ => ðĢĖ) Î Î
    map' ðģ Îī (v i) = ðģ (Îī i)
    map' ðģ Îī (Æ t) = Æ map' ðģ (Îī âŠ _) t
    map' ðģ Îī (ÆĖ t) = ÆĖ map' ðģ (Îī âŠ _) t
    map' ðģ Îī (t â s) = (map' ðģ Îī t) â (map' ðģ Îī s)
instance
    ðĢĖËĒ : Syntax ðĢĖ
    ðĢĖËĒ .var = v
    ðĢĖËĒ .map = map'

-- Naming convention: If both an unmarked and marked version
-- of a term appears, one is named M and the other is named MĖ.
-- But when no ambiguity is present, I use M for both kinds.
variable
    MĖ NĖ : ÎĖ n

-- These two are related:
â_â : ÎĖ n -> Î n
â v x â = v x
â Æ t â = ^ â t â
â ÆĖ t â = ^ â t â
â t â s â = â t â â â s â

â_â : Î n -> ÎĖ n
â v x â = v x
â ^ M â = Æ â M â
â M â N â = â M â â â N â

-- We relate these two:
ââ_ââ : (M : Î n) -> â â M â â âĄ M
ââ v x ââ = refl
ââ ^ M ââ rewrite ââ M ââ = refl
ââ M â N ââ rewrite ââ M ââ | ââ N ââ = refl


private  -- A reflection data structure
    infix 5 â_ââĄ_
    data â_ââĄ_ : ÎĖ n -> Î n -> Set where
        v : â {n} (i : ðĨ n â) -> â v i ââĄ v i
        Æ_ : â MĖ ââĄ M -> â Æ MĖ ââĄ ^ M
        ÆĖ_ : â MĖ ââĄ M -> â ÆĖ MĖ ââĄ ^ M
        _â_ : â MĖ ââĄ M -> â NĖ ââĄ N -> â MĖ â NĖ ââĄ M â N

    reflect : â (MĖ : ÎĖ n) -> â MĖ ââĄ â MĖ â
    reflect (v x) = v x
    reflect (Æ MĖ) = Æ reflect MĖ
    reflect (ÆĖ MĖ) = ÆĖ reflect MĖ
    reflect (MĖ â NĖ) = reflect MĖ â reflect NĖ

    view : â MĖ ââĄ M -> â MĖ â âĄ M
    view (v i) = refl
    view (Æ r) rewrite view r = refl
    view (ÆĖ r) rewrite view r = refl
    view (r â s) rewrite view r | view s = refl

-- For every single step reduction, we can mark the redex:
mark : â {M N : Î n} -> M âķâ N -> ÎĖ n
mark {M = (^ M) â N} (red Îē) = (ÆĖ â M â) â â N â
mark {M = _ â N} (appâ r) = mark r â â N â
mark {M = N â _} (appáĩĢ r) = â N â â mark r
mark (lam r) = Æ mark r

âmark_â : (r : M âķâ N) -> â mark r â âĄ M
âmark_â {M = (^ M) â N} (red Îē) rewrite ââ M ââ | ââ N ââ = refl
âmark_â {M = _ â M} (appâ r) rewrite ââ M ââ | âmark r â = refl
âmark_â {M = M â _} (appáĩĢ r) rewrite ââ M ââ | âmark r â = refl
âmark_â {M = ^ M} (lam r) rewrite âmark r â = refl

-- We prove that the â_â function is a Hom:
private
    instance
        _ = SyntaxĘ· âĶ ðĢĖËĒ âĶ
        _ = SyntaxĘ· âĶ ðĢËĒ âĶ

    instance
        Homââ : Hom â_â
        Homââ .Hvar = refl
        Homââ .Hwed = Hwed'
            where
                Hwed' : âĶ _ : Weakening ðē âĶ (Îī : [ ðē => ðĢĖ ])
                    -> â {Î Î} (Ï : (ðĨ => ðē) Î Î) {i} (t : ðĢĖ Î i)
                    -> â map Îī Ï t â âĄ map (â_â â Îī) Ï â t â
                Hwed' Îī Ï (v x) = refl
                Hwed' Îī Ï (Æ t) rewrite Hwed' Îī (Ï âŠ _) t = refl
                Hwed' Îī Ï (ÆĖ t) rewrite Hwed' Îī (Ï âŠ _) t = refl
                Hwed' Îī Ï (t â s)
                    rewrite Hwed' Îī Ï t | Hwed' Îī Ï s = refl
        Homââ .Hpol Îī Îī' nat wk = Hpol'
            where
                Hpol' : â {Î Î} (Ï : (ðĨ => ðĢĖ) Î Î) {i} (t : ðĢĖ Î i)
                    -> â map Îī Ï t â âĄ map Îī' (â_â â Ï) â t â
                Hpol' Ï (v x) = nat (Ï x)
                Hpol' Ï (Æ t) = cong ^_ $
                    transp (cong (Îŧ u -> â map Îī (Ï âŠ _) t â âĄ map Îī' u â t â) $
                        funext (wk Ï)) $
                    Hpol' (Ï âŠ _) t
                Hpol' Ï (ÆĖ t) = cong ^_ $
                    transp (cong (Îŧ u -> â map Îī (Ï âŠ _) t â âĄ map Îī' u â t â) $
                        funext (wk Ï)) $
                    Hpol' (Ï âŠ _) t
                Hpol' Ï (t â s)
                    rewrite Hpol' Ï t | Hpol' Ï s = refl

-- We make a function that reduces all the marked redexes
Ï : ÎĖ n -> Î n
Ï (v x) = v x
Ï (Æ r) = ^ Ï r
Ï (ÆĖ r) = ^ Ï r  -- This ÆĖ is impossible, so actually writing anything here does the job
Ï ((ÆĖ r) â s) = subst (ðŦ/ Ï s) (Ï r)
Ï (r â s) = Ï r â Ï s

-- On unmarked terms, it does nothing:
Ïâ_â : (M : Î n) -> Ï â M â âĄ M
Ïâ v x â = refl
Ïâ ^ M â rewrite Ïâ M â = refl
Ïâ M â N â with M | Ïâ M â
... | v x    | eq rewrite Ïâ N â = refl
... | ^ M    | eq rewrite Ïâ N â | eq = refl
... | M â M' | eq rewrite Ïâ N â | eq = refl

-- If you mark a term and reduce the marked redex, you get the result back:
Ïmark : (r : M âķâ N) -> Ï (mark r) âĄ N
Ïmark {M = (^ M) â N}  (red Îē)  rewrite Ïâ M â | Ïâ N â       = refl
Ïmark {M = v x â N}    (appáĩĢ r) rewrite Ïmark r               = refl
Ïmark {M = (^ M) â N}  (appáĩĢ r) rewrite Ïmark r | Ïâ M â      = refl
Ïmark {M = M â M' â N} (appáĩĢ r) rewrite Ïmark r | Ïâ M â M' â = refl
Ïmark {M = ^ M}        (lam r)  rewrite Ïmark r               = refl
Ïmark {M = M â N} (appâ r@(red Îē))
    rewrite Ïmark r | Ïâ N â = refl
Ïmark {M = M â N} (appâ r@(appâ _))
    rewrite Ïmark r | Ïâ N â = refl
Ïmark {M = M â N} (appâ r@(appáĩĢ _))
    rewrite Ïmark r | Ïâ N â = refl
Ïmark {M = M â N} (appâ r@(lam _))
    rewrite Ïmark r | Ïâ N â = refl

-- Ï really computes a genuine reduction:
Ïred : (M : ÎĖ n)
    -> â M â âķ Ï M
Ïred (v x) = begin _
Ïred (Æ M) = mapâ lam_ (Ïred M)
Ïred (ÆĖ M) = mapâ lam_ (Ïred M)
Ïred ((v _) â N)     = mapâ appáĩĢ_ (Ïred N)
Ïred (M@(Æ _) â N)   = mapâ appáĩĢ_ (Ïred N) â mapâ appâ_ (Ïred M)
Ïred (M@(_ â _) â N) = mapâ appáĩĢ_ (Ïred N) â mapâ appâ_ (Ïred M)
Ïred ((ÆĖ M) â N)
    = mapâ appáĩĢ_          (Ïred N)
    â mapâ (appâ_ â lam_) (Ïred M)
    â begin _ to _ by red Îē

-- Now we set off to define a reduction relation on ÎĖ
infix 2 _âĖ_ _âķĖâ_ _âķĖ_
data _âĖ_ {n} : ÎĖ n -> ÎĖ n -> Set where
    Îē : â {M : ÎĖ (n âš)} {N : ÎĖ n}
        -> (Æ M) â N âĖ subst (ðŦ/ N) M
    ÎēĖ : â {M : ÎĖ (n âš)} {N : ÎĖ n}
        -> (ÆĖ M) â N âĖ subst (ðŦ/ N) M
data _âķĖâ_ {n} : ÎĖ n -> ÎĖ n -> Set where
    red_ : {M M' : ÎĖ n} -> M âĖ M' -> M âķĖâ M'
    appâ_ : {M M' N : ÎĖ n} -> M âķĖâ M' -> M â N âķĖâ M' â N
    appáĩĢ_ : {M N N' : ÎĖ n} -> N âķĖâ N' -> M â N âķĖâ M â N'
    lam_ : {M M' : ÎĖ (n âš)} -> M âķĖâ M' -> Æ M âķĖâ Æ M'
    lĖam_ : {M M' : ÎĖ (n âš)} -> M âķĖâ M' -> ÆĖ M âķĖâ ÆĖ M'
infixr 9 lĖam_
_âķĖ_ : ÎĖ n -> ÎĖ n -> Set
_âķĖ_ = Trans _âķĖâ_

redââ_â : MĖ âķĖâ NĖ -> â MĖ â âķâ â NĖ â
redââ_â {MĖ = (Æ MĖ) â NĖ} (red Îē)
    = transp  -- We cannot rewrite by (HsubstðŦ/_ NĖ MĖ) because âĪ get eta-expanded
        (cong ((^ â MĖ â) â â NĖ â âķâ_) $
            symm $ HsubstðŦ/_ NĖ MĖ) $
        red Îē
redââ_â {MĖ = (ÆĖ MĖ) â NĖ} (red ÎēĖ)
    = transp
        (cong ((^ â MĖ â) â â NĖ â âķâ_) $
            symm $ HsubstðŦ/_ NĖ MĖ) $
        red Îē
redââ appâ r â = appâ redââ r â
redââ appáĩĢ r â = appáĩĢ redââ r â
redââ lam r â = lam redââ r â
redââ lĖam r â = lam redââ r â

redâ_â : MĖ âķĖ NĖ -> â MĖ â âķ â NĖ â
redâ_â = mapâ redââ_â
