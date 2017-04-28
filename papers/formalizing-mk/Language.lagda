\AgdaHide{
\begin{code}
module Language where

open import Level using (Level; zero; suc; _⊔_)
open import Relation.Binary using (DecSetoid)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; _xor_)
  renaming (not to bnot; _≟_ to _=𝔹_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong₂)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product using (Σ; _×_; proj₁; proj₂; _,_)
open import Data.Sum using (_⊎_)
open import Data.List using (List; []; _∷_; [_])

open import Variables

private
  DT : Set (suc zero)
  DT = DecSetoid zero zero
\end{code}
}

One of the important concepts is that of a \emph{language with variables},
in other words a language with a reasonable definition of substitution.
This requires \emph{variables} to come from a
type which has the structure of a decidable setoid (from the
Agda library \AgdaModule{DecSetoid}, and denoted
\AgdaFunction{DT} below).

A language, expressed as an inductive type, is closed, i.e., cannot be
extended.  If a language does not have variables, we cannot add them.
One solution is to deal with \emph{contexts} as first-class citizens.
While that is likely the best long-term solution, here we have gone with
something simpler:  create another language which does, and show that its
variable-free fragment is equivalent to the original.  As that aspect of
our development is straightforward, albeit tedious, we elide it.

As we are concerned with statements in first-order logic over a
variety of languages, it makes sense to modularize this aspect somewhat.
Note that, as we are building syntax via inductive types, we can either
build these as functors and then use a fixpoint combinator to tie the
knot, or we can just bite the bullet and make one large definition.
For now, we chose the latter.  We do parametrize over a
\emph{ground language with variables}.  In turn, this is defined
as a type parametrized by a decidable setoid along with an evaluation
function into some type \AgdaSymbol{T}.

\begin{code}
record GroundLanguage (T : Set₀) : Set₁ where
  open DecSetoid using (Carrier)
  field
    Lang : DT → Set₀
    value : {V : DT} → Lang V → (Carrier V → T) → T
\end{code}

A logic over a language (with variables), is then also a parametrized
type as well as a parametrized interpretation into types.  The
definition is almost the same, except that a ground language
interprets into \AgdaSymbol{T} and a logic into \AgdaPrimitiveType{Set₀}.

\begin{code}
record LogicOverL (T : Set₀) (L : GroundLanguage T) : Set₁ where
  open DecSetoid using (Carrier)
  field
    Logic : DT → Set₀
    ⟦_⟧_ : ∀ {V} → Logic V → (Carrier V → T) → Set₀
\end{code}

The definition of first logic is then straightforward.

\begin{code}
module FOL {T : Set₀} (L : GroundLanguage T) where
  open DecSetoid using (Carrier)
  open GroundLanguage L
  
  data FOL (V : DT) : Set where
    tt : FOL V
    ff : FOL V
    _and_ : FOL V → FOL V → FOL V
    _or_ : FOL V → FOL V → FOL V
    not : FOL V → FOL V
    _⊃_ : FOL V → FOL V → FOL V
    _==_ : Lang V → Lang V → FOL V
    all : Carrier V → FOL V → FOL V
    exist : Carrier V → FOL V → FOL V

  override : {V : DT} → (Carrier V → T) → Carrier V → T → (Carrier V → T)
  override {V} f x t y with DecSetoid._≟_ V y x
  ... | yes _ = t
  ... | no _  = f y
\end{code}

\noindent We can also prove that \AgdaSymbol{FOL} is a logic
over \AgdaSymbol{L} by providing an interpretation.  Of course,
as we are modeling classical logic into a constructive logic,
we have to use a double-negation embedding.  We also choose to
interpret the logic's equality $\AgdaInductiveConstructor{\_==\_}$ as
\emph{propositional equality}, but we could make that choice a
parameter as well.

\begin{code}
  LoL-FOL : LogicOverL T L
  LoL-FOL = record { Logic = FOL ; ⟦_⟧_ = interp }
   where
    interp : {Var : DT} → FOL Var → (Carrier Var → T) → Set₀
    interp tt env = ⊤
    interp ff env = ⊥
    interp (e and f) env = interp e env × interp f env
    interp (e or f) env = ¬ ¬ (interp e env ⊎ interp f env)
    interp (not e) env = ¬ (interp e env)
    interp (e ⊃ f) env = (interp e env) → (interp f env)
    interp (x == y) env = value x env ≡ value y env
    interp {V} (all x p) env   = ∀ z → interp p (override {V} env x z)
    interp {V} (exist x p) env = ¬ ¬ (Σ T (λ t → interp p (override {V} env x t)))
\end{code}
