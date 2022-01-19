\documentclass{article}
\usepackage[hidelinks]{hyperref}
\usepackage[links]{agda}
% The following packages are needed because unicode
% is translated (using the next set of packages) to
% latex commands. You may need more packages if you
% use more unicode characters:

\usepackage{amssymb}
\usepackage{amsmath}
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage{alphabeta}

%\usepackage{microtype}
%\DisableLigatures[-]{encoding=T1}

\usepackage{bbm}
\usepackage{mathrsfs}
\usepackage{attrib}

% This handles the translation of unicode to latex:
\usepackage{newunicodechar}
\newunicodechar{⊗}{\ensuremath{\otimes}}
\newunicodechar{⊕}{\ensuremath{\oplus}}
\newunicodechar{𝕋}{\ensuremath{\mathbb{T}}}
\newunicodechar{⇒}{\ensuremath{\Rightarrow}}
\newunicodechar{⟶}{\ensuremath{\to}}
\newunicodechar{∋}{\ensuremath{\ni}}
\newunicodechar{◂}{\ensuremath{\mathbin{\triangleleft}}}
\newunicodechar{≪}{\ensuremath{\mathbin{\text{\guillemotleft}}}}
\newunicodechar{∅}{\ensuremath{\varnothing}}
\newunicodechar{𝕫}{\ensuremath{\mathsf{z}}}
\newunicodechar{𝕤}{\ensuremath{\mathsf{s}}}
\newunicodechar{𝕧}{\ensuremath{\mathsf{v}}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{⊢}{\ensuremath{\vdash}}
\newunicodechar{₀}{\ensuremath{_0}}
\newunicodechar{₁}{\ensuremath{_1}}
\newunicodechar{₂}{\ensuremath{_2}}
\newunicodechar{ᵣ}{\ensuremath{_r}}
\newunicodechar{ₛ}{\ensuremath{_s}}
\newunicodechar{ˢ}{\ensuremath{^s}}
\newunicodechar{ʷ}{\ensuremath{^w}}
\newunicodechar{ᶜ}{\ensuremath{^c}}
\newunicodechar{∘}{\ensuremath{\circ}}
\newunicodechar{𝒜}{\ensuremath{\mathscr{A}}}
\newunicodechar{ℬ}{\ensuremath{\mathscr{B}}}
\newunicodechar{𝒞}{\ensuremath{\mathscr{C}}}
\newunicodechar{𝒟}{\ensuremath{\mathscr{D}}}
\newunicodechar{𝓥}{\ensuremath{\mathcal{V}}}
\newunicodechar{𝓣}{\ensuremath{\mathscr{T}}}
\newunicodechar{𝑓}{\ensuremath{\mathit{f}}}
\newunicodechar{𝑔}{\ensuremath{\mathit{g}}}
\newunicodechar{ℭ}{\ensuremath{\mathfrak{C}}}
\newunicodechar{𝔇}{\ensuremath{\mathfrak{D}}}
\newunicodechar{⟦}{\ensuremath{[\![}}
\newunicodechar{⟧}{\ensuremath{]\!]}}
\newunicodechar{⦃}{\ensuremath{\{\!|}}
\newunicodechar{⦄}{\ensuremath{|\!\}}}
\newunicodechar{⇛}{\ensuremath{\Longrightarrow}}
\newunicodechar{ƛ}{\ensuremath{\lambda}}
\newunicodechar{∙}{\ensuremath{\cdot}}
\newunicodechar{≡}{\ensuremath{\equiv}}

\title{Incoherent coherences}
\author{Trebor}
\date{}

\begin{document}
\maketitle
\begin{abstract}
This article explores a generic framework of well-typed and well-scoped syntaxes,
with a signature-axiom approach resembling traditional abstract algebra.
The boilerplate code needed in defining operations on syntaxes is identified
and abstracted away. Some of the frequent boilerplate proofs are also
generalized.
\end{abstract}

This is a literate Agda file, meaning that the code below
is all actually checked and automatically typeset by Agda.
The complete source code can be found at
\url{https://github.com/Trebor-Huang/STLC}.

\begin{code}[hide]
{-# OPTIONS --allow-unsolved-metas #-}
module coh where
open import Preliminaries
open import Agda.Primitive
\end{code}

\section{Conor's Exercise}
\begin{code}
module Conor's-Exercise where
\end{code}

It all starts when one tries to implement \emph{typed} $\lambda$-calculus
in a language with dependent types.

\AgdaTarget{𝕋}
\begin{code}
    data 𝕋 : Set where
        ι    : 𝕋
        _⟶_  : 𝕋 → 𝕋 → 𝕋
    infixr 15 _⟶_
\end{code}

Note that we use the same glyph $\to$ for the Agda function space and
the $\lambda$-calculus function space. The colors are different, but even
without the colors, it should be clear from context.

A context (no pun intended) is simply a snoc-list:

\begin{code}
    Context = List 𝕋
    _ : Context
    _ = ∅ ◂ ι ◂ (ι ⟶ ι)
\end{code}

We use \AgdaInductiveConstructor{\_◂\_} for a visual reminder that
it is a snoc-list.

\begin{code}[hide]
    variable
        σ τ : 𝕋
        Γ Δ Ξ Θ : Context
\end{code}

In this way, we can ensure that our variables are well-typed:

\begin{code}
    infix 5 _∋_
    data _∋_ : Context → 𝕋 → Set where
        𝕫  :            Γ ◂ σ ∋ σ
        𝕤_ :   Γ ∋ τ →  Γ ◂ σ ∋ τ
\end{code}

Now we can define well-typed terms:

\begin{code}
    infix 5 _⊢_
    data _⊢_ : Context → 𝕋 → Set where
        var  :      Γ  ∋ σ                  → Γ ⊢ σ
        app  :      Γ  ⊢ σ ⟶ τ     → Γ ⊢ σ  → Γ ⊢ τ
        lam  : Γ ◂  σ  ⊢ τ                  → Γ ⊢ σ ⟶ τ
\end{code}

The type system of Agda now ensures that every term is well-typed,
blurring the distinction between syntax --- what terms are well-formed,
and semantics --- what meanings the terms have. Let's look at some
examples:

\begin{code}
    I : ∅ ⊢ σ ⟶ σ
    I = lam (var 𝕫)

    K : ∅ ⊢ σ ⟶ τ ⟶ σ
    K = lam (lam (var (𝕤 𝕫)))
\end{code}

So far so good. But just \emph{defining} terms is surely not enough,
we need to be able to \emph{manipulate} them. The most fundamental
operation on syntax with variable bindings, is substitution:

\begin{code}
    Substitution : Context → Context → Set
    Substitution Γ Δ = ∀ {σ} → Γ ∋ σ → Δ ⊢ σ

    Transformation : Context → Context → Set
    Transformation Γ Δ = ∀ {σ} → Γ ⊢ σ → Δ ⊢ σ
\end{code}

Let's go right into it:

\begin{code}
    subs₁ : Substitution Γ Δ → Transformation Γ Δ
    ---- subscript₁ for "first attempt"
    subs₁ s (var i)      = s i
    subs₁ s (app t₁ t₂)  = app (subs₁ s t₁) (subs₁ s t₂)
\end{code}

The powerful type system helps us write the program: By asking
Agda to do a case-split on the term being transformed, we immediately
get the required branches. Agda can also automatically generate the
correct term to write in the first two branches. But in the third branch
there is a problem:

\begin{code}
    subs₁ s (lam t) = lam (subs₁ {!   !} t)
\end{code}

We need a way to ``push in'' an extra variable. And here we go:

\begin{code}
    push₁ : Substitution Γ Δ → Substitution (Γ ◂ σ) (Δ ◂ σ)
    push₁ σ 𝕫      = var 𝕫
    push₁ σ (𝕤 i)  = {!   !}
\end{code}

This in turn requires us to weaken a term:

\begin{code}
    weaken₁ : Γ ⊢ σ → Γ ◂ τ ⊢ σ
    weaken₁ (var i)      = var (𝕤 i)
    weaken₁ (app t₁ t₂)  = app (weaken₁ t₁) (weaken₁ t₂)
    weaken₁ (lam t)      = lam {!   !}
\end{code}

The first two cases are still easy, but the \AgdaInductiveConstructor{lam}
case is problematic. We need to push in yet another variable!

It turns out that we need to do this in two steps. First, we deal with
variable renamings only:

\begin{code}
    Renaming : Context → Context → Set
    Renaming Γ Δ = ∀ {σ} → Γ ∋ σ → Δ ∋ σ

    weakenᵣ : Renaming Γ Δ → Renaming (Γ ◂ σ) (Δ ◂ σ)
    weakenᵣ r 𝕫      = 𝕫
    weakenᵣ r (𝕤 i)  = 𝕤 r i

    rename : Renaming Γ Δ → Transformation Γ Δ
    rename r (var i)      = var (r i)
    rename r (app t₁ t₂)  = app (rename r t₁) (rename r t₂)
    rename r (lam t)      = lam (rename (weakenᵣ r) t)
\end{code}

The \AgdaInductiveConstructor{lam} case now goes through. And we can
finish off the development:

\begin{code}
    weakenₛ : Substitution Γ Δ → Substitution (Γ ◂ σ) (Δ ◂ σ)
    weakenₛ s 𝕫      = var 𝕫
    weakenₛ s (𝕤 i)  = rename 𝕤_ (s i)

    subs : Substitution Γ Δ → Transformation Γ Δ
    subs s (var i)      = s i
    subs s (app t₁ t₂)  = app (subs s t₁) (subs s t₂)
    subs s (lam t)      = lam (subs (weakenₛ s) t)
\end{code}

In retrospect, the reason that we have to do this in two steps, is that
\AgdaDatatype{\_⊢\_} is \emph{defined} in two steps: It requires \AgdaDatatype{\_∋\_}
in its definition.

However, comparing the two pairs of functions we can see some sort of pattern.
It is called \emph{weakening-then-traversal} in exercise 19 of \cite{conor}. And let's do that.

\section{Abstraction and Generality}
\begin{code}
module Abstraction (I : Set) where
\end{code}

In this section, we will work with an abstract parameter \AgdaArgument{I}
instead of \AgdaDatatype{𝕋} in the previous section. We can start by
noticing the similarity in the type signature:

\AgdaTarget{Scope, Morph}
\begin{code}
    Scope = (Γ : List I) (i : I) → Set
    Morph = (Γ Δ : List I) → Set
\end{code}
\begin{code}[hide]
    private variable
        Γ Δ Θ Ξ : List I
        i j k l : I
        𝒜 ℬ 𝒞 𝒟 𝒱 𝒲 : Scope
\end{code}

\AgdaDatatype{\_⊢\_} and \AgdaDatatype{\_∋\_} both have type \AgdaFunction{Scope}.
And \AgdaFunction{Renaming}, \AgdaFunction{Substitution} and
\AgdaFunction{Transformation} all have type \AgdaFunction{Morph}. The name
``scope'' comes from \cite{gallais}.

In the untyped case, \AgdaArgument{I} is simply the singleton type (``Untyped is
uni-typed''). This, in abstract nonsense, makes \AgdaFunction{Scope} the type of
\textbf{presheafs} on the category of renamings. \AgdaFunction{Morph} is
then natural transformations between the presheafs.%
\footnote{Of course, we haven't imposed the functorial laws yet, so
they are better described as \emph{raw} presheafs and natural transformations.
I will not spell out the categorical details, since I'm not going to
use the category-theoretic language in an essential way. More can be read at
\cite{presheaf}.}

Now we define the standard well-typed variables, which can be regarded
as the image of the Yoneda embedding:

\AgdaTarget{𝓥}
\begin{code}
    infix 5 _∋_
    data _∋_ : Scope where
        𝕫   :          Γ ◂ i  ∋ i
        𝕤_  : Γ ∋ i →  Γ ◂ j  ∋ i
    infixr 100 𝕤_

    𝓥 = _∋_
\end{code}
\begin{code}[hide]
    private variable
        v w : 𝓥 Γ i
\end{code}

Next, some combinators that already emerged in the last section.

\AgdaTarget{⇒, [, ], ⇛, ⟦, ⟧}
\begin{code}
    infix 4 _⇒_
    _⇒_ : Scope → Scope → Morph
    (𝒞 ⇒ 𝒟) Γ Δ = ∀ {i} → 𝒞 Γ i → 𝒟 Δ i

    [_] : Morph → Set
    [ ℭ ] = ∀ {Γ} → ℭ Γ Γ

    infixr 3 _⇛_
    _⇛_ : Morph → Morph → Morph
    (ℭ ⇛ 𝔇) Γ Δ = ℭ Γ Δ → 𝔇 Γ Δ

    ⟦_⟧ : Morph → Set
    ⟦ ℭ ⟧ = ∀ {Γ Δ} → ℭ Γ Δ
\end{code}

With these, we can redefine \AgdaFunction{Renaming}, \AgdaFunction{Substitution} and
\AgdaFunction{Transformation} uniformly:

\begin{code}
    module _ (𝒞 : Scope) where
        Renaming Substitution Transformation : Morph

        Renaming        = 𝓥  ⇒ 𝓥
        Substitution    = 𝓥  ⇒ 𝒞
        Transformation  = 𝒞  ⇒ 𝒞
\end{code}

In \cite{gallais}, a notion of ``generic syntax'' is built, and
a datatype \AgdaDatatype{Desc} is used to describe syntaxes in general.
This is very much like building a datatype \AgdaDatatype{Poly} to describe
polynomial functors, and generating the initial algebras once and for all:

\begin{code}
    module Generic where
        data Poly : Set₁ where
            Const   : Set → Poly
            Id      : Poly
            _⊕_     : Poly → Poly → Poly
            _⊗_     : Poly → Poly → Poly

        ---- interprets Poly into Functor (i.e. Set → Set)
        interp : Poly → (Set → Set)
        interp (Const B) A  = B
        interp Id A         = A
        interp (f ⊕ g) A    = interp f A + interp g A
        interp (f ⊗ g) A    = interp f A × interp g A

        data Fix (f : Poly) : Set where
            fix : interp f (Fix f) → Fix f
\end{code}

One can implement a generic \AgdaFunction{cata} on \AgdaDatatype{Fix}.
This is left as an exercise for the reader. You can find the answer at \cite{tutorial}.

In the same spirit, \cite{gallais} described how to manipulate and reason about
generic syntax. In abstract nonsense, this can be recast as initial algebras
of functors in the aforementioned presheaf category.
But apart from polynomial functors, we get to use more functors related to
the binding structure. In particular, the weakening operation induces
a new functor that corresponds to \AgdaInductiveConstructor{lam}.

This way of describing things is cool, clean and intuitive.
Since we build up a universe of syntaxes inductively, we have absolute
control over them. And theorems etc. can be proven by induction on
the syntaxes, which is also convenient.
However, it is more suited to theorem proving than to practical programming:
For the same reason, we almost always prefer using inductive datatypes
to using \AgdaDatatype{Fix}, even though they are equivalent in expressivity!%
\footnote{No, they are not. But non-dependent inductive datatypes can
be represented with \AgdaDatatype{Fix}, once it is appropriately extended
to allow infinitary sums and products.}\footnote{Also, with the Univalence
Axiom, we can seamlessly transport all the theorems from there to our
homemade syntax (e.g. as defined in our first section), thus taking
the best part of both sides.}

Therefore, I shall now tread this road less taken. And let us see what
plight awaits us!

\section{The Road Less Taken}

Instead of building a universe on which we have absolute control, let's
choose to \emph{place restrictions} on a large existing universe so we have
\emph{minimum} control. Now, all we know is that we have a \AgdaFunction{Scope}.
What more can we say about it?

Well, let's do weakening first:

\AgdaTarget{Weakening, weaken}
\begin{code}
    record Weakening (𝒞 : Scope) : Set where
        field
            weaken :      (𝓥 ⇒ 𝒞) Γ         Δ
                → ∀ i  →  (𝓥 ⇒ 𝒞) (Γ ◂ i)   (Δ ◂ i)
    open Weakening ⦃...⦄ public
\end{code}

Note that the $⦃\dots⦄$ tells Agda to treat this record type similarly to
\emph{typeclasses} as in Haskell. We can declare instances of this typeclass,
which will be automatically used to infer arguments.

\begin{code}[hide]
    infixl 50 _≪_
    _≪_ : ⦃ Weakening 𝒞 ⦄
        → ∀ {Γ Δ}  → (𝓥 ⇒ 𝒞) Γ        Δ
        → ∀ i      → (𝓥 ⇒ 𝒞) (Γ ◂ i)  (Δ ◂ i)
\end{code}

A convenient infix:
\AgdaTarget{\_≪\_}
\begin{code}
    _≪_ = weaken
\end{code}

Sanity check: \AgdaFunction{𝓥} itself can be weakened:
\begin{code}
    instance
        𝓥ʷ : Weakening 𝓥
        𝓥ʷ .weaken ρ i 𝕫 = 𝕫
        𝓥ʷ .weaken ρ i (𝕤 v) = 𝕤 (ρ v)
\end{code}

Good. Next, we can start to extract the common pattern in the
renaming and substitution process. If the code is rewritten with our
combinators, the signature of \AgdaFunction{rename} would be something
like
%
\begin{code}[hide]
    renameType : Scope → Set
    renameType 𝒞 =
\end{code}
\begin{code}[inline]
        ⟦ 𝓥 ⇒ 𝓥 ⇛ 𝒞 ⇒ 𝒞 ⟧
\end{code}
. And \AgdaFunction{subst} would be of type
%
\begin{code}[hide]
    substType : Scope → Set
    substType 𝒞 =
\end{code}
\begin{code}[inline]
        ⟦ 𝓥 ⇒ 𝒞 ⇛ 𝒞 ⇒ 𝒞 ⟧
\end{code}
.

Interesting! So looking at the types only, we would naturally come
to the generalization
%
\begin{code}[hide]
    genType : Scope → Scope → Set
    genType 𝒞 𝒜 =
\end{code}
\begin{code}[inline]
        ⟦ 𝓥 ⇒ 𝒜 ⇛ 𝒞 ⇒ 𝒞 ⟧
\end{code}
. Now of course, we can't define this for arbitrary \AgdaArgument{𝒜}.
So what more would we need? We have an assignment of variables to \AgdaArgument{𝒜},
and we are given an expression of \AgdaArgument{𝒞}. We need to replace
all the free variables in the expression according to the assignment.
So we definitely need a conversion
%
\begin{code}[hide]
    convType : Scope → Scope → Set
    convType 𝒞 𝒜 =
\end{code}
\begin{code}[inline*]
        [ 𝒜 ⇒ 𝒞 ]
\end{code}
from the assigned \AgdaArgument{𝒜}'s to \AgdaArgument{𝒞}'s.

During the process, we also need to be able to push into binders.
Therefore we also need to ``weaken''. This brings us to the complete
type signature:
\begin{code}[hide]
    mapType : Scope → Scope → Set
    mapType 𝒞 𝒜 =
\end{code}
\begin{code}
            ⦃ Weakening 𝒜 ⦄
        →   [ 𝒜 ⇒ 𝒞 ]
        →   ⟦ 𝓥 ⇒ 𝒜 ⇛ 𝒞 ⇒ 𝒞 ⟧
\end{code}

Last but not least, we need to ensure that every variable is also
a legitimate term, otherwise we wouldn't have much to work with. Packing
all of these up gives us another typeclass:

\AgdaTarget{Syntax, var, map}
\begin{code}
    record Syntax (𝒞 : Scope) : Set₁ where
        field
            var  : [ 𝓥 ⇒ 𝒞 ]
            map  :  ⦃ Weakening 𝒜 ⦄
                →   [ 𝒜 ⇒ 𝒞 ]
                →   ⟦ 𝓥 ⇒ 𝒜 ⇛ 𝒞 ⇒ 𝒞 ⟧
\end{code}

Now we can implement renaming and substitution based on the typeclass
methods, and when we are using them in practice, we only need to provide
the implementation of \AgdaField{var} and \AgdaField{map}. Sweet!

Renaming is a piece of cake:

\AgdaTarget{rename}
\begin{code}
        rename : ⟦ 𝓥 ⇒ 𝓥 ⇛ 𝒞 ⇒ 𝒞 ⟧
        rename = map var
\end{code}

Note that since we already told Agda that \AgdaFunction{𝓥} has
\AgdaField{weaken}ing, we don't need to mention that at all here.

Next, before we start to implement substitution, we need:

\begin{code}
        Syntaxʷ : Weakening 𝒞
        Syntaxʷ .weaken σ i 𝕫 = var 𝕫
        Syntaxʷ .weaken σ i (𝕤 v) = rename 𝕤_ (σ v)
\end{code}

For technical reasons, it is not very convenient for us to make it an
instance. So for substitution, we will tell Agda about \AgdaFunction{Weakening}
manually.

\AgdaTarget{subst}
\begin{code}
        subst : ⟦ 𝓥 ⇒ 𝒞 ⇛ 𝒞 ⇒ 𝒞 ⟧
        subst = map id
            where instance _ = Syntaxʷ
\end{code}

And there you have it. Finally, since we often need to substitute
only one variable (the rightmost one in the context), we make a little
helper function:

\begin{code}
        𝕫/_ : 𝒞 Γ i → (𝓥 ⇒ 𝒞) (Γ ◂ i) Γ
        (𝕫/ t) 𝕫 = t
        (𝕫/ t) (𝕤 v) = var v
        infixr 6 𝕫/_
    open Syntax ⦃...⦄ public
\end{code}

Let's see how things goes if we rewrite the simply typed $\lambda$-calculus
with the tools we just developed. First, we need to show that
\AgdaFunction{𝓥} itself is an instance of \AgdaFunction{Syntax}:

\begin{code}
    instance
        𝓥ˢ : Syntax 𝓥
        𝓥ˢ .var = id
        𝓥ˢ .map 𝑓 σ v = 𝑓 (σ v)
\end{code}
\begin{code}[hide]
module TestLambda where
    data 𝕋 : Set where
        ι    : 𝕋
        _⟶_  : 𝕋 → 𝕋 → 𝕋
    infixr 15 _⟶_
    private variable
        i j : 𝕋
        Γ Δ Θ : List 𝕋
        𝒜 ℬ 𝒞 𝒟 : List 𝕋 -> 𝕋 -> Set
\end{code}

Recall that we worked in a parameterized module.
Now we instantiate the parameter with the concrete type \AgdaDatatype{𝕋}.

\begin{code}
    open Abstraction 𝕋
    infix 5 _⊢_
    data _⊢_ : Scope where
        𝕧_   :      Γ  ∋ i                  → Γ ⊢ i
        _∙_  :      Γ  ⊢ i ⟶ j     → Γ ⊢ i  → Γ ⊢ j
        ƛ_   : Γ ◂  i  ⊢ j                  → Γ ⊢ i ⟶ j
    infixl 20 _∙_
    infixr 10 ƛ_
    infixr 100 𝕧_

    𝓣 = _⊢_
\end{code}

Again, we used $\lambda$ for both Agda functions and $\lambda$-calculus
functions. Now we give the implementation for the \AgdaFunction{Syntax}
structure:
\begin{code}
    instance
        𝓣ˢ : Syntax 𝓣
        𝓣ˢ .var = 𝕧_
\end{code}

The \AgdaField{var} case is easy. What about \AgdaField{map}?

\begin{code}
        𝓣ˢ .map = helper
         where
             helper : ⦃ Weakening 𝒜 ⦄
                 → [ 𝒜 ⇒ 𝓣 ]
                 → ⟦ 𝓥 ⇒ 𝒜 ⇛ 𝓣 ⇒ 𝓣 ⟧
\end{code}

Agda helps us fill in the goals pretty easily:
\begin{code}
             helper 𝑓 σ (𝕧 v)    = 𝑓 (σ v)
             helper 𝑓 σ (t ∙ s)  = helper 𝑓 σ t ∙ helper 𝑓 σ s
             helper 𝑓 σ (ƛ t)    = ƛ helper 𝑓 (σ ≪ _) t
\end{code}

We now get substitution for free! For example:
\begin{code}
    A : ∅ ◂ ι ⟶ ι ⊢ ι ⟶ ι
    A = ƛ 𝕧 𝕤 𝕫 ∙ (𝕧 𝕤 𝕫 ∙ 𝕧 𝕫)

    B : ∅ ⊢ ι ⟶ ι
    B = ƛ 𝕧 𝕫

    A[B] = subst (𝕫/ B) A
    _ : A[B] ≡ ƛ (ƛ 𝕧 𝕫) ∙ ((ƛ 𝕧 𝕫) ∙ 𝕧 𝕫)
    _ = refl
\end{code}

\section{Higher-order Homomorphisms}

\begin{code}
module HoHom (I : Set) where
\end{code}
\begin{code}[hide]
    open Abstraction I
    private variable
        Γ Δ Θ Ξ : List I
        i j k l : I
        𝒜 ℬ 𝒞 𝒟 𝒱 𝒲 : Scope
        v : 𝓥 Γ i
\end{code}

From this section on, we move from \emph{doing} things to \emph{proving} things.
For instance, in a classic proof of the Church-Rosser theorem, a technique
is used that ``colors'' specific $\lambda$'s to track their behavior in
reduction. An indispensable lemma of that proof is that
\emph{substitution commutes with color erasure}. Suppose $\Lambda$
is the set of uncolored terms, and $\overline\Lambda$ is the set of
terms with color. $\lfloor \cdot \rfloor : \overline\Lambda \to \Lambda$
erases the colors. Then the lemma to be proved is
$$ \left\lfloor t (x \mapsto s) \right\rfloor = \lfloor t \rfloor ( x \mapsto \lfloor s \rfloor ). $$
This looks suspiciously similar to \emph{homomorphisms} in abstract algebra.
For example a group homomorphism $\phi$ satisfies
$$\phi(x \cdot y) = \phi(x) \cdot \phi(y).$$
One crucial difference: The definition of group homomorphisms is directly
concerned about group multiplication, which is a ``primitive'' concept; On
the other hand, substitution
is defined in terms of \AgdaField{var} and \AgdaField{map}.
So it is clear that we need to come up with an equation in terms of these
two primitives.

\AgdaTarget{Hom}
\begin{code}
    record Hom ⦃ 𝒞ˢ : Syntax 𝒞 ⦄ ⦃ 𝒟ˢ : Syntax 𝒟 ⦄
        (𝑓 : [ 𝒞 ⇒ 𝒟 ]) : Set₁ where
        private instance
            _ = Syntaxʷ ⦃ 𝒞ˢ ⦄
            _ = Syntaxʷ ⦃ 𝒟ˢ ⦄
        field
\end{code}

What may we say about \AgdaArgument{𝑓}? For \AgdaField{var} it's easy.
We just need to take care of some implicit arguments:
\AgdaTarget{Hvar}
\begin{code}
            Hvar : 𝑓 {Γ} {i} (var v) ≡ var v
\end{code}

But there is some difficulty for \AgdaField{map}, because it is a
\emph{higher-order} function, acting on other functions. How do we write
out the homomorphism requirements for high-order structures? For concreteness,
let's take an example.

We define a \textbf{fixoid} to be a set $X$ together with a functional
$F : (X \to X) \to X$ on it. This has no practical use whatsoever,%
\footnote{Actually, if we impose that $F$ sends functions to their
fixpoints: $$F(f) = f(F(f)),$$then this becomes what is called a
\textbf{fixed-point space}. It is trivial for discrete spaces, but once
we impose a topology it becomes interesting. For example, any closed interval
endowed with the real topology is a fixed-point space.}
and is only
intended as an example for us to discuss what higher-order homomorphisms
should be like.

Take two fixoids, $(X, F)$ and $(Y, G)$. What makes a function $\phi : X \to Y$
a homomorphism? The first reasonable guess is that we have an equation
of the form
$$ \phi(F(?)) = G(?). $$
What should we put in the arguments? There should be an $f : X \to X$
and a $g : Y \to Y$. But surely they can't be arbitrary. What should be
the relation between them? Looking at the type signatures, let's go for
the obvious:
$$\forall x, \quad\phi(f(x)) = g(\phi(x)).$$
So, if we collect everything, we get the definition:

A \textbf{homomorphism} between fixoids $(X, F)$ and $(Y, G)$ is a function
$\phi : X \to Y$ such that for every pair of functions $f : X \to X$
and $g : Y \to Y$,
$$\phi \circ f = g\circ\phi  \implies  \phi(F(f)) = G(g).$$

In fact, any other ``reasonable'' conditions we may impose are already
implied by this one! The proof is quite combinatorial, and is left as an
exercise for the reader.

\section{Incoherent Coherences}

In a similar spirit, after meditating at the type signature for a while,
one may come up with such a condition for \AgdaField{map}:
\begin{code}
            Hnat : ⦃ 𝒜ʷ : Weakening 𝒜 ⦄ (δ : [ 𝒜 ⇒ 𝒞 ])
                → ∀ {Γ Δ} (σ : (𝓥 ⇒ 𝒜) Γ Δ) {i} (v : 𝒞 Γ i)
                → 𝑓 (map δ σ v) ≡ (map (𝑓 ∘ δ) σ) (𝑓 v)
\end{code}

It looks quite intimidating, but the first two lines are just setup.
It is pretty much what is expected, but unfortunately it is not enough.
In the degenerate case that $𝒜 = 𝒞$, it turns out that we need an additional
rule...

\begin{code}
            Hpol : (δ : [ 𝒞 ⇒ 𝒞 ]) (δ' : [ 𝒟 ⇒ 𝒟 ])
                → (nat : ∀ {Γ σ} (t : 𝒞 Γ σ)
                    → 𝑓 (δ t) ≡ δ' (𝑓 t))   ---- !
                → (wk : ∀ {Γ Δ} (σ : (𝓥 ⇒ 𝒞) Γ Δ) {i j} (v : 𝓥 _ i)
                    → 𝑓 ((σ ≪ j) v) ≡ ((𝑓 ∘ σ) ≪ j) v)
                → ∀ {Γ Δ} (σ : (𝓥 ⇒ 𝒞) Γ Δ) {i} (t : 𝒞 Γ i)
                → 𝑓 (map δ σ t) ≡ map δ' (𝑓 ∘ σ) (𝑓 t)   ---- !
\end{code}

... It's even more intimidating. But only the two lines marked by comments
matters. The first says that the two \AgdaArgument{δ}'s satisfy a similar
condition to the equation for $f$ and $g$ in the case of fixoids.
The second is \emph{slightly} different to \AgdaField{Hnat}, but also reasonable.

The argument \AgdaArgument{wk} is actually not necessary, and we will
eliminate it. But when implementing this typeclass method, it helps to
make inductions go through.

\begin{code}[hide]
        private
            fH𝕫/_ : (t : 𝒞 Γ i) (v : 𝓥 (Γ ◂ i) j)
                → 𝑓 ((𝕫/ t) v) ≡ (𝕫/ 𝑓 t) v
            (fH𝕫/ t) 𝕫 = refl
            (fH𝕫/ t) (𝕤 v) = Hvar

        H𝕫/_ : ∀ (t : 𝒞 Γ i)
            → (λ {j} → 𝑓 {i = j} ∘ (𝕫/ t)) ≡ 𝕫/ 𝑓 t
        H𝕫/ t = funext' \ _ → funext (fH𝕫/ t)

        private
            fHvar : (\{Γ i} → 𝑓 {Γ} {i} ∘ var) ≡ var
            fHvar =
                funext' \ _ →
                funext' \ _ →
                funext  \ _ → Hvar
\end{code}

But after some straightforward definitions, we can prove the desired lemma
for \AgdaFunction{rename}:
\begin{code}
        Hrename : ∀ {Γ Δ} (ρ : (𝓥 ⇒ 𝓥) Γ Δ)
            → ∀ {i} (t : 𝒞 Γ i)
            → 𝑓 (rename ρ t) ≡ rename ρ (𝑓 t)
        Hrename ρ t rewrite symm fHvar = Hnat var ρ t
\end{code}
\begin{code}[hide]
        Hweaken : ∀ (σ : (𝓥 ⇒ 𝒞) Γ Δ) {i j} (v : Γ ◂ i ∋ j)
            → 𝑓 ((σ ≪ i) v) ≡ ((𝑓 ∘ σ) ≪ i) v
        Hweaken σ 𝕫 = Hvar
        Hweaken σ (𝕤 v) = Hrename 𝕤_ (σ v)

        private
            fHweaken : (σ : (𝓥 ⇒ 𝒞) Γ Δ)
                → 𝑓 {i = j} ∘ (σ ≪ i) ≡ (𝑓 ∘ σ) ≪ i
            fHweaken σ = funext (Hweaken σ)

        Hmap : (δ : [ 𝒞 ⇒ 𝒞 ]) (δ' : [ 𝒟 ⇒ 𝒟 ])
            → (nat : ∀ {Γ σ} (t : 𝒞 Γ σ)
                → 𝑓 (δ t) ≡ δ' (𝑓 t))
            → ∀ {Γ Δ} (σ : (𝓥 ⇒ 𝒞) Γ Δ) {i} (t : 𝒞 Γ i)
            → 𝑓 (map δ σ t) ≡ map δ' (𝑓 ∘ σ) (𝑓 t)
        Hmap δ δ' nat = Hpol δ δ' nat (λ σ v → Hweaken σ v)
\end{code}
And \AgdaFunction{subst}:
\begin{code}
        Hsubst : ∀ {Γ Δ} (σ : (𝓥 ⇒ 𝒞) Γ Δ)
            → ∀ {i} (t : 𝒞 Γ i)
            → 𝑓 (subst σ t) ≡ subst (𝑓 ∘ σ) (𝑓 t)
        Hsubst σ t = Hmap id id (λ _ → refl) σ t

        Hsubst𝕫/_ : ∀ {Γ i j} (t : 𝒞 Γ i) (t' : 𝒞 (Γ ◂ i) j)
            → 𝑓 (subst (𝕫/ t) t') ≡ subst (𝕫/ 𝑓 t) (𝑓 t')
        Hsubst𝕫/_ t t' rewrite Hsubst (𝕫/ t) t' | H𝕫/ t = refl
\end{code}

Note that \AgdaFunction{Hmap} is a version of \AgdaField{Hnat}, but with
the \AgdaArgument{wk} argument removed. Also, we used the function
extensionality axiom here. The details are hidden.

\begin{code}
    open Hom ⦃...⦄ public
\end{code}

You can see an example of usage in the accompanying repository.

Apart from homomorphisms, we are also interested in the interactions of
substitution with \emph{itself}. This is the celebrated \textbf{substitution
lemma}:
$$t(x \mapsto s_1)(y \mapsto s_2) = t(y \mapsto s_2)(x\mapsto s_1(y \mapsto s_2))$$
under the condition that $x$ is not free in $s_2$. To prove this, we similarly
need to prove a version for renamings first. One would naturally ask whether
these two versions can be unified.

Here the coherence conditions get really nasty. The final goal is clear:
\begin{code}[hide]
    record Stable (𝒞 : Scope) ⦃ 𝒞ˢ : Syntax 𝒞 ⦄ : Set₁ where
        field
            map-comp : ⦃ 𝒜ʷ : Weakening 𝒜 ⦄
                -> ⦃ 𝒟ˢ : Syntax 𝒟 ⦄ 
                -> (𝑔 : [ 𝒟 ⇒ 𝒞 ])
                -> (𝑓 : [ 𝒜 ⇒ 𝒟 ])
                -> ∀ {Γ Δ Θ}
                -> (σ : (𝓥 ⇒ 𝒜) Γ Δ) (δ : (𝓥 ⇒ 𝒟) Θ Γ)
                -> let instance _ = Syntaxʷ ⦃ 𝒟ˢ ⦄ in 
                ∀ {i} (t : 𝒞 Θ i) ->
\end{code}
\begin{code}
                    map (𝑔 ∘ 𝑓) σ (map 𝑔 δ t) ≡ map 𝑔 (map 𝑓 σ ∘ δ) t
\end{code}

With suitably instantiated \AgdaArgument{𝑓} and
\AgdaArgument{𝑔}, this equation encapsulates both the renaming and substitution
lemmas.
But it is unclear what conditions should be imposed on \AgdaArgument{𝑓} and
\AgdaArgument{𝑔}. How should we proceed? Is this a dead end, and should we
now turn to more conventional methods of manipulating syntax with binding?
This is left as an \emph{exercise} for the reader.

\begin{quotation}
It is a question of foundations of mathematics, rather than mathematics itself;
or, at least, I hope so. The reply is left to the reader as an exercise.
(This phrase always means that the writer cannot do the problem himself.)
\attrib{\cite{difficult}, p. 15.}
\end{quotation}

\begin{thebibliography}{10}

\bibitem{conor} Conor McBride.
\emph{Epigram: Practical Programming with Dependent Types}.
Available at \url{http://www.e-pig.org/downloads/epigram-notes.pdf}.

\bibitem{gallais} Guillaume Allais, Robert Atkey, James Chapman, Conor McBride, James McKinna.
\emph{A type- and scope-safe universe of syntaxes with binding: their semantics and proofs}.
Available at \url{https://gallais.github.io/pdf/generic-syntax.pdf}.

\bibitem{tutorial} Ulf Norell, James Chapman.
\emph{Dependently Typed Programming in Agda}.
Available at \url{http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf}.

\bibitem{presheaf} Marcelo Fiore, Gordon Plotkin, Daniele Turi.
\emph{Abstract Syntax and Variable Binding}.
Available at \url{https://homepages.inf.ed.ac.uk/gdp/publications/Abstract_Syn.pdf} (Extended Abstract).

\bibitem{difficult} Carl E. Linderholm.
\emph{Mathematics Made Difficult}.
Butler \& Tanner Ltd, Frome and London, 1971.

\end{thebibliography}

\end{document}
