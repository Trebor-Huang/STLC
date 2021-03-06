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
\newunicodechar{โ}{\ensuremath{\otimes}}
\newunicodechar{โ}{\ensuremath{\oplus}}
\newunicodechar{๐}{\ensuremath{\mathbb{T}}}
\newunicodechar{โ}{\ensuremath{\Rightarrow}}
\newunicodechar{โถ}{\ensuremath{\to}}
\newunicodechar{โ}{\ensuremath{\ni}}
\newunicodechar{โ}{\ensuremath{\mathbin{\triangleleft}}}
\newunicodechar{โช}{\ensuremath{\mathbin{\text{\guillemotleft}}}}
\newunicodechar{โ}{\ensuremath{\varnothing}}
\newunicodechar{๐ซ}{\ensuremath{\mathsf{z}}}
\newunicodechar{๐ค}{\ensuremath{\mathsf{s}}}
\newunicodechar{๐ง}{\ensuremath{\mathsf{v}}}
\newunicodechar{โ}{\ensuremath{\mathnormal\forall}}
\newunicodechar{โข}{\ensuremath{\vdash}}
\newunicodechar{โ}{\ensuremath{_0}}
\newunicodechar{โ}{\ensuremath{_1}}
\newunicodechar{โ}{\ensuremath{_2}}
\newunicodechar{แตฃ}{\ensuremath{_r}}
\newunicodechar{โ}{\ensuremath{_s}}
\newunicodechar{หข}{\ensuremath{^s}}
\newunicodechar{สท}{\ensuremath{^w}}
\newunicodechar{แถ}{\ensuremath{^c}}
\newunicodechar{โ}{\ensuremath{\circ}}
\newunicodechar{๐}{\ensuremath{\mathscr{A}}}
\newunicodechar{โฌ}{\ensuremath{\mathscr{B}}}
\newunicodechar{๐}{\ensuremath{\mathscr{C}}}
\newunicodechar{๐}{\ensuremath{\mathscr{D}}}
\newunicodechar{๐ฅ}{\ensuremath{\mathcal{V}}}
\newunicodechar{๐ฃ}{\ensuremath{\mathscr{T}}}
\newunicodechar{๐}{\ensuremath{\mathit{f}}}
\newunicodechar{๐}{\ensuremath{\mathit{g}}}
\newunicodechar{โญ}{\ensuremath{\mathfrak{C}}}
\newunicodechar{๐}{\ensuremath{\mathfrak{D}}}
\newunicodechar{โฆ}{\ensuremath{[\![}}
\newunicodechar{โง}{\ensuremath{]\!]}}
\newunicodechar{โฆ}{\ensuremath{\{\!|}}
\newunicodechar{โฆ}{\ensuremath{|\!\}}}
\newunicodechar{โ}{\ensuremath{\Longrightarrow}}
\newunicodechar{ฦ}{\ensuremath{\lambda}}
\newunicodechar{โ}{\ensuremath{\cdot}}
\newunicodechar{โก}{\ensuremath{\equiv}}

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

\AgdaTarget{๐}
\begin{code}
    data ๐ : Set where
        ฮน    : ๐
        _โถ_  : ๐ โ ๐ โ ๐
    infixr 15 _โถ_
\end{code}

Note that we use the same glyph $\to$ for the Agda function space and
the $\lambda$-calculus function space. The colors are different, but even
without the colors, it should be clear from context.

A context (no pun intended) is simply a snoc-list:

\begin{code}
    Context = List ๐
    _ : Context
    _ = โ โ ฮน โ (ฮน โถ ฮน)
\end{code}

We use \AgdaInductiveConstructor{\_โ\_} for a visual reminder that
it is a snoc-list.

\begin{code}[hide]
    variable
        ฯ ฯ : ๐
        ฮ ฮ ฮ ฮ : Context
\end{code}

In this way, we can ensure that our variables are well-typed:

\begin{code}
    infix 5 _โ_
    data _โ_ : Context โ ๐ โ Set where
        ๐ซ  :            ฮ โ ฯ โ ฯ
        ๐ค_ :   ฮ โ ฯ โ  ฮ โ ฯ โ ฯ
\end{code}

Now we can define well-typed terms:

\begin{code}
    infix 5 _โข_
    data _โข_ : Context โ ๐ โ Set where
        var  :      ฮ  โ ฯ                  โ ฮ โข ฯ
        app  :      ฮ  โข ฯ โถ ฯ     โ ฮ โข ฯ  โ ฮ โข ฯ
        lam  : ฮ โ  ฯ  โข ฯ                  โ ฮ โข ฯ โถ ฯ
\end{code}

The type system of Agda now ensures that every term is well-typed,
blurring the distinction between syntax --- what terms are well-formed,
and semantics --- what meanings the terms have. Let's look at some
examples:

\begin{code}
    I : โ โข ฯ โถ ฯ
    I = lam (var ๐ซ)

    K : โ โข ฯ โถ ฯ โถ ฯ
    K = lam (lam (var (๐ค ๐ซ)))
\end{code}

So far so good. But just \emph{defining} terms is surely not enough,
we need to be able to \emph{manipulate} them. The most fundamental
operation on syntax with variable bindings, is substitution:

\begin{code}
    Substitution : Context โ Context โ Set
    Substitution ฮ ฮ = โ {ฯ} โ ฮ โ ฯ โ ฮ โข ฯ

    Transformation : Context โ Context โ Set
    Transformation ฮ ฮ = โ {ฯ} โ ฮ โข ฯ โ ฮ โข ฯ
\end{code}

Let's go right into it:

\begin{code}
    subsโ : Substitution ฮ ฮ โ Transformation ฮ ฮ
    ---- subscriptโ for "first attempt"
    subsโ s (var i)      = s i
    subsโ s (app tโ tโ)  = app (subsโ s tโ) (subsโ s tโ)
\end{code}

The powerful type system helps us write the program: By asking
Agda to do a case-split on the term being transformed, we immediately
get the required branches. Agda can also automatically generate the
correct term to write in the first two branches. But in the third branch
there is a problem:

\begin{code}
    subsโ s (lam t) = lam (subsโ {!   !} t)
\end{code}

We need a way to ``push in'' an extra variable. And here we go:

\begin{code}
    pushโ : Substitution ฮ ฮ โ Substitution (ฮ โ ฯ) (ฮ โ ฯ)
    pushโ ฯ ๐ซ      = var ๐ซ
    pushโ ฯ (๐ค i)  = {!   !}
\end{code}

This in turn requires us to weaken a term:

\begin{code}
    weakenโ : ฮ โข ฯ โ ฮ โ ฯ โข ฯ
    weakenโ (var i)      = var (๐ค i)
    weakenโ (app tโ tโ)  = app (weakenโ tโ) (weakenโ tโ)
    weakenโ (lam t)      = lam {!   !}
\end{code}

The first two cases are still easy, but the \AgdaInductiveConstructor{lam}
case is problematic. We need to push in yet another variable!

It turns out that we need to do this in two steps. First, we deal with
variable renamings only:

\begin{code}
    Renaming : Context โ Context โ Set
    Renaming ฮ ฮ = โ {ฯ} โ ฮ โ ฯ โ ฮ โ ฯ

    weakenแตฃ : Renaming ฮ ฮ โ Renaming (ฮ โ ฯ) (ฮ โ ฯ)
    weakenแตฃ r ๐ซ      = ๐ซ
    weakenแตฃ r (๐ค i)  = ๐ค r i

    rename : Renaming ฮ ฮ โ Transformation ฮ ฮ
    rename r (var i)      = var (r i)
    rename r (app tโ tโ)  = app (rename r tโ) (rename r tโ)
    rename r (lam t)      = lam (rename (weakenแตฃ r) t)
\end{code}

The \AgdaInductiveConstructor{lam} case now goes through. And we can
finish off the development:

\begin{code}
    weakenโ : Substitution ฮ ฮ โ Substitution (ฮ โ ฯ) (ฮ โ ฯ)
    weakenโ s ๐ซ      = var ๐ซ
    weakenโ s (๐ค i)  = rename ๐ค_ (s i)

    subs : Substitution ฮ ฮ โ Transformation ฮ ฮ
    subs s (var i)      = s i
    subs s (app tโ tโ)  = app (subs s tโ) (subs s tโ)
    subs s (lam t)      = lam (subs (weakenโ s) t)
\end{code}

In retrospect, the reason that we have to do this in two steps, is that
\AgdaDatatype{\_โข\_} is \emph{defined} in two steps: It requires \AgdaDatatype{\_โ\_}
in its definition.

However, comparing the two pairs of functions we can see some sort of pattern.
It is called \emph{weakening-then-traversal} in exercise 19 of \cite{conor}. And let's do that.

\section{Abstraction and Generality}
\begin{code}
module Abstraction (I : Set) where
\end{code}

In this section, we will work with an abstract parameter \AgdaArgument{I}
instead of \AgdaDatatype{๐} in the previous section. We can start by
noticing the similarity in the type signature:

\AgdaTarget{Scope, Morph}
\begin{code}
    Scope = (ฮ : List I) (i : I) โ Set
    Morph = (ฮ ฮ : List I) โ Set
\end{code}
\begin{code}[hide]
    private variable
        ฮ ฮ ฮ ฮ : List I
        i j k l : I
        ๐ โฌ ๐ ๐ ๐ฑ ๐ฒ : Scope
\end{code}

\AgdaDatatype{\_โข\_} and \AgdaDatatype{\_โ\_} both have type \AgdaFunction{Scope}.
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

\AgdaTarget{๐ฅ}
\begin{code}
    infix 5 _โ_
    data _โ_ : Scope where
        ๐ซ   :          ฮ โ i  โ i
        ๐ค_  : ฮ โ i โ  ฮ โ j  โ i
    infixr 100 ๐ค_

    ๐ฅ = _โ_
\end{code}
\begin{code}[hide]
    private variable
        v w : ๐ฅ ฮ i
\end{code}

Next, some combinators that already emerged in the last section.

\AgdaTarget{โ, [, ], โ, โฆ, โง}
\begin{code}
    infix 4 _โ_
    _โ_ : Scope โ Scope โ Morph
    (๐ โ ๐) ฮ ฮ = โ {i} โ ๐ ฮ i โ ๐ ฮ i

    [_] : Morph โ Set
    [ โญ ] = โ {ฮ} โ โญ ฮ ฮ

    infixr 3 _โ_
    _โ_ : Morph โ Morph โ Morph
    (โญ โ ๐) ฮ ฮ = โญ ฮ ฮ โ ๐ ฮ ฮ

    โฆ_โง : Morph โ Set
    โฆ โญ โง = โ {ฮ ฮ} โ โญ ฮ ฮ
\end{code}

With these, we can redefine \AgdaFunction{Renaming}, \AgdaFunction{Substitution} and
\AgdaFunction{Transformation} uniformly:

\begin{code}
    module _ (๐ : Scope) where
        Renaming Substitution Transformation : Morph

        Renaming        = ๐ฅ  โ ๐ฅ
        Substitution    = ๐ฅ  โ ๐
        Transformation  = ๐  โ ๐
\end{code}

In \cite{gallais}, a notion of ``generic syntax'' is built, and
a datatype \AgdaDatatype{Desc} is used to describe syntaxes in general.
This is very much like building a datatype \AgdaDatatype{Poly} to describe
polynomial functors, and generating the initial algebras once and for all:

\begin{code}
    module Generic where
        data Poly : Setโ where
            Const   : Set โ Poly
            Id      : Poly
            _โ_     : Poly โ Poly โ Poly
            _โ_     : Poly โ Poly โ Poly

        ---- interprets Poly into Functor (i.e. Set โ Set)
        interp : Poly โ (Set โ Set)
        interp (Const B) A  = B
        interp Id A         = A
        interp (f โ g) A    = interp f A + interp g A
        interp (f โ g) A    = interp f A ร interp g A

        data Fix (f : Poly) : Set where
            fix : interp f (Fix f) โ Fix f
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
    record Weakening (๐ : Scope) : Set where
        field
            weaken :      (๐ฅ โ ๐) ฮ         ฮ
                โ โ i  โ  (๐ฅ โ ๐) (ฮ โ i)   (ฮ โ i)
    open Weakening โฆ...โฆ public
\end{code}

Note that the $โฆ\dotsโฆ$ tells Agda to treat this record type similarly to
\emph{typeclasses} as in Haskell. We can declare instances of this typeclass,
which will be automatically used to infer arguments.

\begin{code}[hide]
    infixl 50 _โช_
    _โช_ : โฆ Weakening ๐ โฆ
        โ โ {ฮ ฮ}  โ (๐ฅ โ ๐) ฮ        ฮ
        โ โ i      โ (๐ฅ โ ๐) (ฮ โ i)  (ฮ โ i)
\end{code}

A convenient infix:
\AgdaTarget{\_โช\_}
\begin{code}
    _โช_ = weaken
\end{code}

Sanity check: \AgdaFunction{๐ฅ} itself can be weakened:
\begin{code}
    instance
        ๐ฅสท : Weakening ๐ฅ
        ๐ฅสท .weaken ฯ i ๐ซ = ๐ซ
        ๐ฅสท .weaken ฯ i (๐ค v) = ๐ค (ฯ v)
\end{code}

Good. Next, we can start to extract the common pattern in the
renaming and substitution process. If the code is rewritten with our
combinators, the signature of \AgdaFunction{rename} would be something
like
%
\begin{code}[hide]
    renameType : Scope โ Set
    renameType ๐ =
\end{code}
\begin{code}[inline]
        โฆ ๐ฅ โ ๐ฅ โ ๐ โ ๐ โง
\end{code}
. And \AgdaFunction{subst} would be of type
%
\begin{code}[hide]
    substType : Scope โ Set
    substType ๐ =
\end{code}
\begin{code}[inline]
        โฆ ๐ฅ โ ๐ โ ๐ โ ๐ โง
\end{code}
.

Interesting! So looking at the types only, we would naturally come
to the generalization
%
\begin{code}[hide]
    genType : Scope โ Scope โ Set
    genType ๐ ๐ =
\end{code}
\begin{code}[inline]
        โฆ ๐ฅ โ ๐ โ ๐ โ ๐ โง
\end{code}
. Now of course, we can't define this for arbitrary \AgdaArgument{๐}.
So what more would we need? We have an assignment of variables to \AgdaArgument{๐},
and we are given an expression of \AgdaArgument{๐}. We need to replace
all the free variables in the expression according to the assignment.
So we definitely need a conversion
%
\begin{code}[hide]
    convType : Scope โ Scope โ Set
    convType ๐ ๐ =
\end{code}
\begin{code}[inline*]
        [ ๐ โ ๐ ]
\end{code}
from the assigned \AgdaArgument{๐}'s to \AgdaArgument{๐}'s.

During the process, we also need to be able to push into binders.
Therefore we also need to ``weaken''. This brings us to the complete
type signature:
\begin{code}[hide]
    mapType : Scope โ Scope โ Set
    mapType ๐ ๐ =
\end{code}
\begin{code}
            โฆ Weakening ๐ โฆ
        โ   [ ๐ โ ๐ ]
        โ   โฆ ๐ฅ โ ๐ โ ๐ โ ๐ โง
\end{code}

Last but not least, we need to ensure that every variable is also
a legitimate term, otherwise we wouldn't have much to work with. Packing
all of these up gives us another typeclass:

\AgdaTarget{Syntax, var, map}
\begin{code}
    record Syntax (๐ : Scope) : Setโ where
        field
            var  : [ ๐ฅ โ ๐ ]
            map  :  โฆ Weakening ๐ โฆ
                โ   [ ๐ โ ๐ ]
                โ   โฆ ๐ฅ โ ๐ โ ๐ โ ๐ โง
\end{code}

Now we can implement renaming and substitution based on the typeclass
methods, and when we are using them in practice, we only need to provide
the implementation of \AgdaField{var} and \AgdaField{map}. Sweet!

Renaming is a piece of cake:

\AgdaTarget{rename}
\begin{code}
        rename : โฆ ๐ฅ โ ๐ฅ โ ๐ โ ๐ โง
        rename = map var
\end{code}

Note that since we already told Agda that \AgdaFunction{๐ฅ} has
\AgdaField{weaken}ing, we don't need to mention that at all here.

Next, before we start to implement substitution, we need:

\begin{code}
        Syntaxสท : Weakening ๐
        Syntaxสท .weaken ฯ i ๐ซ = var ๐ซ
        Syntaxสท .weaken ฯ i (๐ค v) = rename ๐ค_ (ฯ v)
\end{code}

For technical reasons, it is not very convenient for us to make it an
instance. So for substitution, we will tell Agda about \AgdaFunction{Weakening}
manually.

\AgdaTarget{subst}
\begin{code}
        subst : โฆ ๐ฅ โ ๐ โ ๐ โ ๐ โง
        subst = map id
            where instance _ = Syntaxสท
\end{code}

And there you have it. Finally, since we often need to substitute
only one variable (the rightmost one in the context), we make a little
helper function:

\begin{code}
        ๐ซ/_ : ๐ ฮ i โ (๐ฅ โ ๐) (ฮ โ i) ฮ
        (๐ซ/ t) ๐ซ = t
        (๐ซ/ t) (๐ค v) = var v
        infixr 6 ๐ซ/_
    open Syntax โฆ...โฆ public
\end{code}

Let's see how things goes if we rewrite the simply typed $\lambda$-calculus
with the tools we just developed. First, we need to show that
\AgdaFunction{๐ฅ} itself is an instance of \AgdaFunction{Syntax}:

\begin{code}
    instance
        ๐ฅหข : Syntax ๐ฅ
        ๐ฅหข .var = id
        ๐ฅหข .map ๐ ฯ v = ๐ (ฯ v)
\end{code}
\begin{code}[hide]
module TestLambda where
    data ๐ : Set where
        ฮน    : ๐
        _โถ_  : ๐ โ ๐ โ ๐
    infixr 15 _โถ_
    private variable
        i j : ๐
        ฮ ฮ ฮ : List ๐
        ๐ โฌ ๐ ๐ : List ๐ -> ๐ -> Set
\end{code}

Recall that we worked in a parameterized module.
Now we instantiate the parameter with the concrete type \AgdaDatatype{๐}.

\begin{code}
    open Abstraction ๐
    infix 5 _โข_
    data _โข_ : Scope where
        ๐ง_   :      ฮ  โ i                  โ ฮ โข i
        _โ_  :      ฮ  โข i โถ j     โ ฮ โข i  โ ฮ โข j
        ฦ_   : ฮ โ  i  โข j                  โ ฮ โข i โถ j
    infixl 20 _โ_
    infixr 10 ฦ_
    infixr 100 ๐ง_

    ๐ฃ = _โข_
\end{code}

Again, we used $\lambda$ for both Agda functions and $\lambda$-calculus
functions. Now we give the implementation for the \AgdaFunction{Syntax}
structure:
\begin{code}
    instance
        ๐ฃหข : Syntax ๐ฃ
        ๐ฃหข .var = ๐ง_
\end{code}

The \AgdaField{var} case is easy. What about \AgdaField{map}?

\begin{code}
        ๐ฃหข .map = helper
         where
             helper : โฆ Weakening ๐ โฆ
                 โ [ ๐ โ ๐ฃ ]
                 โ โฆ ๐ฅ โ ๐ โ ๐ฃ โ ๐ฃ โง
\end{code}

Agda helps us fill in the goals pretty easily:
\begin{code}
             helper ๐ ฯ (๐ง v)    = ๐ (ฯ v)
             helper ๐ ฯ (t โ s)  = helper ๐ ฯ t โ helper ๐ ฯ s
             helper ๐ ฯ (ฦ t)    = ฦ helper ๐ (ฯ โช _) t
\end{code}

We now get substitution for free! For example:
\begin{code}
    A : โ โ ฮน โถ ฮน โข ฮน โถ ฮน
    A = ฦ ๐ง ๐ค ๐ซ โ (๐ง ๐ค ๐ซ โ ๐ง ๐ซ)

    B : โ โข ฮน โถ ฮน
    B = ฦ ๐ง ๐ซ

    A[B] = subst (๐ซ/ B) A
    _ : A[B] โก ฦ (ฦ ๐ง ๐ซ) โ ((ฦ ๐ง ๐ซ) โ ๐ง ๐ซ)
    _ = refl
\end{code}

\section{Higher-order Homomorphisms}

\begin{code}
module HoHom (I : Set) where
\end{code}
\begin{code}[hide]
    open Abstraction I
    private variable
        ฮ ฮ ฮ ฮ : List I
        i j k l : I
        ๐ โฌ ๐ ๐ ๐ฑ ๐ฒ : Scope
        v : ๐ฅ ฮ i
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
    record Hom โฆ ๐หข : Syntax ๐ โฆ โฆ ๐หข : Syntax ๐ โฆ
        (๐ : [ ๐ โ ๐ ]) : Setโ where
        private instance
            _ = Syntaxสท โฆ ๐หข โฆ
            _ = Syntaxสท โฆ ๐หข โฆ
        field
\end{code}

What may we say about \AgdaArgument{๐}? For \AgdaField{var} it's easy.
We just need to take care of some implicit arguments:
\AgdaTarget{Hvar}
\begin{code}
            Hvar : ๐ {ฮ} {i} (var v) โก var v
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
            Hnat : โฆ ๐สท : Weakening ๐ โฆ (ฮด : [ ๐ โ ๐ ])
                โ โ {ฮ ฮ} (ฯ : (๐ฅ โ ๐) ฮ ฮ) {i} (v : ๐ ฮ i)
                โ ๐ (map ฮด ฯ v) โก (map (๐ โ ฮด) ฯ) (๐ v)
\end{code}

It looks quite intimidating, but the first two lines are just setup.
It is pretty much what is expected, but unfortunately it is not enough.
In the degenerate case that $๐ = ๐$, it turns out that we need an additional
rule...

\begin{code}
            Hpol : (ฮด : [ ๐ โ ๐ ]) (ฮด' : [ ๐ โ ๐ ])
                โ (nat : โ {ฮ ฯ} (t : ๐ ฮ ฯ)
                    โ ๐ (ฮด t) โก ฮด' (๐ t))   ---- !
                โ (wk : โ {ฮ ฮ} (ฯ : (๐ฅ โ ๐) ฮ ฮ) {i j} (v : ๐ฅ _ i)
                    โ ๐ ((ฯ โช j) v) โก ((๐ โ ฯ) โช j) v)
                โ โ {ฮ ฮ} (ฯ : (๐ฅ โ ๐) ฮ ฮ) {i} (t : ๐ ฮ i)
                โ ๐ (map ฮด ฯ t) โก map ฮด' (๐ โ ฯ) (๐ t)   ---- !
\end{code}

... It's even more intimidating. But only the two lines marked by comments
matters. The first says that the two \AgdaArgument{ฮด}'s satisfy a similar
condition to the equation for $f$ and $g$ in the case of fixoids.
The second is \emph{slightly} different to \AgdaField{Hnat}, but also reasonable.

The argument \AgdaArgument{wk} is actually not necessary, and we will
eliminate it. But when implementing this typeclass method, it helps to
make inductions go through.

\begin{code}[hide]
        private
            fH๐ซ/_ : (t : ๐ ฮ i) (v : ๐ฅ (ฮ โ i) j)
                โ ๐ ((๐ซ/ t) v) โก (๐ซ/ ๐ t) v
            (fH๐ซ/ t) ๐ซ = refl
            (fH๐ซ/ t) (๐ค v) = Hvar

        H๐ซ/_ : โ (t : ๐ ฮ i)
            โ (ฮป {j} โ ๐ {i = j} โ (๐ซ/ t)) โก ๐ซ/ ๐ t
        H๐ซ/ t = funext' \ _ โ funext (fH๐ซ/ t)

        private
            fHvar : (\{ฮ i} โ ๐ {ฮ} {i} โ var) โก var
            fHvar =
                funext' \ _ โ
                funext' \ _ โ
                funext  \ _ โ Hvar
\end{code}

But after some straightforward definitions, we can prove the desired lemma
for \AgdaFunction{rename}:
\begin{code}
        Hrename : โ {ฮ ฮ} (ฯ : (๐ฅ โ ๐ฅ) ฮ ฮ)
            โ โ {i} (t : ๐ ฮ i)
            โ ๐ (rename ฯ t) โก rename ฯ (๐ t)
        Hrename ฯ t rewrite symm fHvar = Hnat var ฯ t
\end{code}
\begin{code}[hide]
        Hweaken : โ (ฯ : (๐ฅ โ ๐) ฮ ฮ) {i j} (v : ฮ โ i โ j)
            โ ๐ ((ฯ โช i) v) โก ((๐ โ ฯ) โช i) v
        Hweaken ฯ ๐ซ = Hvar
        Hweaken ฯ (๐ค v) = Hrename ๐ค_ (ฯ v)

        private
            fHweaken : (ฯ : (๐ฅ โ ๐) ฮ ฮ)
                โ ๐ {i = j} โ (ฯ โช i) โก (๐ โ ฯ) โช i
            fHweaken ฯ = funext (Hweaken ฯ)

        Hmap : (ฮด : [ ๐ โ ๐ ]) (ฮด' : [ ๐ โ ๐ ])
            โ (nat : โ {ฮ ฯ} (t : ๐ ฮ ฯ)
                โ ๐ (ฮด t) โก ฮด' (๐ t))
            โ โ {ฮ ฮ} (ฯ : (๐ฅ โ ๐) ฮ ฮ) {i} (t : ๐ ฮ i)
            โ ๐ (map ฮด ฯ t) โก map ฮด' (๐ โ ฯ) (๐ t)
        Hmap ฮด ฮด' nat = Hpol ฮด ฮด' nat (ฮป ฯ v โ Hweaken ฯ v)
\end{code}
And \AgdaFunction{subst}:
\begin{code}
        Hsubst : โ {ฮ ฮ} (ฯ : (๐ฅ โ ๐) ฮ ฮ)
            โ โ {i} (t : ๐ ฮ i)
            โ ๐ (subst ฯ t) โก subst (๐ โ ฯ) (๐ t)
        Hsubst ฯ t = Hmap id id (ฮป _ โ refl) ฯ t

        Hsubst๐ซ/_ : โ {ฮ i j} (t : ๐ ฮ i) (t' : ๐ (ฮ โ i) j)
            โ ๐ (subst (๐ซ/ t) t') โก subst (๐ซ/ ๐ t) (๐ t')
        Hsubst๐ซ/_ t t' rewrite Hsubst (๐ซ/ t) t' | H๐ซ/ t = refl
\end{code}

Note that \AgdaFunction{Hmap} is a version of \AgdaField{Hnat}, but with
the \AgdaArgument{wk} argument removed. Also, we used the function
extensionality axiom here. The details are hidden.

\begin{code}
    open Hom โฆ...โฆ public
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
    record Stable (๐ : Scope) โฆ ๐หข : Syntax ๐ โฆ : Setโ where
        field
            map-comp : โฆ ๐สท : Weakening ๐ โฆ
                -> โฆ ๐หข : Syntax ๐ โฆ 
                -> (๐ : [ ๐ โ ๐ ])
                -> (๐ : [ ๐ โ ๐ ])
                -> โ {ฮ ฮ ฮ}
                -> (ฯ : (๐ฅ โ ๐) ฮ ฮ) (ฮด : (๐ฅ โ ๐) ฮ ฮ)
                -> let instance _ = Syntaxสท โฆ ๐หข โฆ in 
                โ {i} (t : ๐ ฮ i) ->
\end{code}
\begin{code}
                    map (๐ โ ๐) ฯ (map ๐ ฮด t) โก map ๐ (map ๐ ฯ โ ฮด) t
\end{code}

With suitably instantiated \AgdaArgument{๐} and
\AgdaArgument{๐}, this equation encapsulates both the renaming and substitution
lemmas.
But it is unclear what conditions should be imposed on \AgdaArgument{๐} and
\AgdaArgument{๐}. How should we proceed? Is this a dead end, and should we
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
