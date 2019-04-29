This is the (partial) story of encoding certain kinds of knowledge
in Agda. More importantly, the story of \textbf{deriving} a lot
of knowledge \emph{mechanically}.

This story will be told through examples, shown in what a human would
traditionally write without tool support. We do have a couple of
prototypes (one in ocaml, the other in emacs lisp & common lisp)
that automates this, but they are both syntactically awkward and
thus not as well suited for clear communication.

(
 Proposal: https://github.com/alhassy/next-700-module-systems-proposal
 Demo: https://www.youtube.com/watch?v=NYOOF9xKBz8&feature=youtu.be
)

\AgdaHide{
\begin{code}
module AgdaMeta where

open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary
import Function as F
open F using (id; _∘_)
open import Agda.Primitive
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ; _+_; _>_; s≤s; z≤n)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)


open ≡-Reasoning
\end{code}
}

Our primary example will be Monoid:
%<*theory>
\begin{code}
record Monoid : Set₁ where
  field
    -- a type or sort
    Carrier    : Set₀

    -- some operations
    Id         : Carrier
    _⨾_        : Carrier → Carrier → Carrier

    -- some equations
    left-unit  : ∀ {x}     → Id ⨾ x ≡ x
    right-unit : ∀ {x}     → x ⨾ Id ≡ x
    assoc      : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
\end{code}
%</theory>

Sometimes we need to produce phrases involving multiple monoids;
we thus introduce the following decorations.

It would be nice if we could “generate” such tediousness.

%<*renaming>
\begin{code}
module Monoid₁ (M : Monoid) where
  open Monoid M public renaming
    ( Carrier    to Carrier₁
    ; Id         to Id₁
    ; _⨾_        to _⨾₁_
    ; left-unit  to left-unit₁
    ; right-unit to right-unit₁
    ; assoc      to assoc₁
    )

module Monoid₂ (M : Monoid) where
  open Monoid M public renaming
    ( Carrier    to Carrier₂
    ; Id         to Id₂
    ; _⨾_        to _⨾₂_
    ; left-unit  to left-unit₂
    ; right-unit to right-unit₂
    ; assoc      to assoc₂
    )
\end{code}
%</renaming>
-- Monoid₃, Monoid₄, etc, …
\end{code}

A Monoid has a type, along with a distinguished point in that type
and a (total) binary operation over that type. There are also three
axioms: That the point is a left and right unit for the operation,
and that the operation is associative. Note that we choose to use
propositional equality for the axioms.

( Alternatively: A monoid is a structure “over” a type.
  We will return to this alternative approach later. )

In general, we will here consider particular kinds of \emph{theories},
for which we know how to manipulate definitions. These are not
particularly restrictive as most theories from traditional Algebra
fit.  Specifically, we'll look closely at
\emph{1-sorted finitary equational theories}, meaning that
we have
\begin{itemize}
\item a single carrier set (1-sorted)
  --for which we will uniformly refer to as “Carrier”.
\item we declare finitely many symbols, denoting operations,
each with arity $≥ 0$
\item axioms of the form
  \[ ∀ x y z \;\bullet\; lhs-term ≡ rhs-term \]
\end{itemize}
Naturally, each one of these can be generalized, but each
generalization brings in non-trivial difficulties that obscure
the utility of the common core.

For later convenience, let us call each kind of definition
\textbf{sorts}, \textbf{operations} and \textbf{equations}
respectively.

The above coincides
exactly with \textsf{Universal Algebra} as initiated by
Alfred North Whitehead in his 1898 book \textit{A Treatise of Universal
Algebra}.

Our motto here:

\begin{centering}
\Large “Make easy things easy!”
\end{centering}

A lot of CS research focuses on the other end of the spectrum,
perhaps aptly phrased as \emph{“make hard things feasible”}. Our aim
is to create tools for humans to \emph{automate drudgery} so that
they may spend more time on aspects where creativity and insight
are actually needed. (•̀ᴗ•́)و

Let us proceed to see many examples of information that can be
derived automatically or with very little user intervention.
To aid in showing that things are not specific to
\AgdaRecord{Monoid}, it is useful to have a second example in
hand; it is also useful for this example to be ``unknown'' so
that particular characteristics of the structure, or familiarity
with the structure, do not obscure things. For this purpose,
\AgdaRecord{Squag} will work nicely:
\begin{code}
record Squag : Set₁ where
  constructor sq
  field
    Carrier       : Set₀
    _⨾_           : Carrier → Carrier → Carrier
    idempotent    : ∀ x → x ⨾ x ≡ x
    commutative   : ∀ x y → x ⨾ y ≡ y ⨾ x
    antiAbsorbent : ∀ x y → x ⨾ (x ⨾ y) ≡ y
\end{code}

\fbox{\textbf{MA: You mention Squag but everything below is about Monoid!? }}

We now turn to some mechanically derivable notions
--for which there is sadly no machine support, yet, in Agda.
\begin{code}
module Derived where
\end{code}

First, there is a general notion of homomorphism between
theories: A mapping from the carrier of one theory to
the other, that \emph{preserves} each of the operations. It is
customary to shorten the name to $\AgdaRecord{Hom}$.
%<*hom>
\begin{code}
record Hom (A B : Monoid) : Set₁ where
  open Monoid₁ A; open Monoid₂ B
  field
    mor     : Carrier₁ → Carrier₂
    pres-Id : mor Id₁ ≡ Id₂
    pres-⨾  : ∀ x y → mor (x ⨾₁ y) ≡ (mor x) ⨾₂ (mor y)

-- “Apply” a homomorphism onto an element
infixr 20 _$_
_$_ : {A B : Monoid} → Hom A B →
      (Monoid.Carrier A → Monoid.Carrier B)
_$_ = Hom.mor
\end{code}
%</hom>

The above makes fundamental use of what is often called
(in the Universal Algebra literature) the \emph{signature}
of the theory:
%<*sig>
\begin{code}
record Signature : Set₁ where
  field
    Carrier : Set₀
    Id      : Carrier
    _⨾_     : Carrier → Carrier → Carrier
\end{code}
%</sig>
Of course, in a dependently-typed setting, all records, including Monoid itself, are
also called signatures, which can unfortunately lead to
confusion. What is important to notice here is that it ought to
be possible to write the follow TemplateHaskell-like meta-program:

\begin{pseudocode}
derive Signature = filter (not equations) ''Monoid
\end{pseudocode}

Observe how each item (field) of \AgdaRecord{Hom}
comes from one of \AgdaRecord{Signature}. This generalizes
``on the nose'' for other theories.  So homomorphisms can be
given generically by
\begin{pseudocode}
derive Hom foo = apply
  { sorts      |-> map
  ; operations |-> preserve
  } (filter (not equations) foo)
\end{pseudocode}

\fbox{\textbf{YS: The syntax for "derive Hom foo" assume we have the following:
1. A language on the declarations level: - classify declarations as sorts, operations or axioms - define operations like map and preserve
2. A language that uses the one above to generate useful constructions, like signature and homomorphisms
In this case, I don't see why we have two a derive function that take Hom or Signature as arguments. My suggestion:
hom foo = apply
  { input f1 f2 : foo
    sorts |-> map
    operations |-> preserve
  }
Then, the function hom would be triggered by calling
derive hom foo
}}

For example, we can look at what equality of two
homomorphisms could be. So we compute the ``signature''
of \AgdaRecord{Hom} and insist that each field be
appropritely related.  In particular, for functions,
this is going to be pointwise:

%<*hom-eq1>
\begin{code}
_∼_ : {A B : Set} (f g : A → B) → Set
f ∼ g = ∀ a → f a ≡ g a

record Hom-Equality {A B : Monoid} (F G : Hom A B) : Set where
  field
    equal : Hom.mor F ∼ Hom.mor G

_≋_ = Hom-Equality
\end{code}
%</hom-eq1>
The astute Agda code may instead suggest the following terse definition.

%<*hom-eq2>
\begin{code}
Hom-Equality′ : ∀ {A B : Monoid} (F G : Hom A B) → Set
Hom-Equality′ F G = Hom.mor F ∼ Hom.mor G
\end{code}
%</hom-eq2>

However, we use a “record” presentation as it generalises to other
derived constructs and thus makes the subsequent derivatives below appear
mechanically derivable. That is, we want to make it as clear as possible
that these could be automatically dervied --simplifications like this
could then be add ons.

Other similar notions can also be defined. A minimalist version
of \emph{isomorphism} requires a (forward) homomorphism
between two monoids, and a mere inverse function. This is because
one can then prove that such a function is necessarily a homomorphism.
\begin{code}
record Isomorphism (A B : Monoid) : Set₁ where
  open Monoid
  open Hom
  field
    A⇒B : Hom A B
    g : Carrier B → Carrier A
    f∘g≡id : (mor A⇒B ∘ g) ∼ id
    g∘f≡id : (g ∘ mor A⇒B) ∼ id

  inv-is-Hom : Hom B A
  inv-is-Hom = record
    { mor = g
    ; pres-Id = trans (sym (cong g (pres-Id A⇒B))) (g∘f≡id (Id A))
    ; pres-⨾ = λ x y →  trans (cong g (sym (cong₂ (_⨾_ B) (f∘g≡id x) (f∘g≡id y))))
               (trans (cong g (sym (pres-⨾ A⇒B (g x) (g y))))
               (g∘f≡id _))
    }
\end{code}

\fbox{\textbf{MA: In general this is not true?}}
{\textbf{JC to MA: take a close look at the proof, which can be cleaned up, and
you'll that it is generic. Each line just needs n-ary cong and preservation for
validity}
If a structure preserving operation has an inverse, the inverse may not be structure
preserving, yeah? If so, then this particular presentation does not appear amicable
to mechanical derivation.

From that, it is useful to create abbreviations for
endomorphisms and automorphisms:
\begin{code}
Endomorphism : Monoid → Set₁
Endomorphism A = Hom A A

Automorphism : Monoid → Set₁
Automorphism A = Isomorphism A A
\end{code}

Another generic concept is that of \AgdaRecord{Kernel} of a
homorphism, which is the set of pairs of points that map to
the same value.
%<*kernel>
\begin{code}
record Kernel {A B : Monoid} (F : Hom A B) : Set₁ where
  open Monoid A
  field
    x    : Carrier
    y    : Carrier
    cond : F $ x ≡ F $ y
\end{code}
%</kernel>
\AgdaRecord{Kernel} is essentially generic, and can be derived
as a template -- unlike previous definitions, which really do need
simple but ``real'' programs to be run on the representations.

It is then possible to prove (generically) that this
induces an equivalence relation (on $A$) which is furthermore
a congruence, which means that this can be used, at least in a
classical setting, to form quotients.

Cartesian products also exist generically.
%<*product>
\begin{code}
record _×M_ (A B : Monoid) : Set₂ where
   field
     -- There is an object:
     ProdM : Monoid

     -- Along with two maps to the orginal arguments:
     Proj1 : Hom ProdM A
     Proj2 : Hom ProdM B
\end{code}
%</product>
Such that any other two maps to the orginal arguments
necessarily factor through some unique mapping called ⟨_,_⟩.
\begin{code}
record IsProduct{A B : Monoid} (C : A ×M B) : Set₂ where
   open _×M_ C
   field
     ⟨_,_⟩ : ∀{M : Monoid} (l : Hom M A) (r : Hom M B) → Hom M ProdM
     factor₁ : ∀{M : Monoid} {l : Hom M A} {r : Hom M B} → Hom.mor l ∼ (Hom.mor Proj1 ∘ Hom.mor ⟨ l , r ⟩)
     factor₂ : ∀{M : Monoid} {l : Hom M A} {r : Hom M B} → Hom.mor r ∼ (Hom.mor Proj2 ∘ Hom.mor ⟨ l , r ⟩)
\end{code}
For now, we ignore these since they're not of much interest to the task at hand.

Above we desribed what a cartesian produced “looks like”
--what constitutes such a constrution. Now we turn to actually
forming an instance of such a construction.

%<*make-prod>
\begin{code}
Make-Cartesian-Product : (A : Monoid) → (B : Monoid) → A ×M B
Make-Cartesian-Product A B =
  let
    open Monoid₁ A
    open Monoid₂ B
  in
  record
  { ProdM = record
              { Carrier    = Carrier₁ × Carrier₂
              ; Id         = Id₁ , Id₂
              ; _⨾_        = zip _⨾₁_ _⨾₂_
              ; left-unit  = cong₂ _,_ left-unit₁ left-unit₂
              ; right-unit = cong₂ _,_ right-unit₁ right-unit₂
              ; assoc      = cong₂ _,_ assoc₁ assoc₂
              }
  ; Proj1 = record { mor = proj₁ ; pres-Id = refl ; pres-⨾ = λ _ _ → refl }
  ; Proj2 = record { mor = proj₂ ; pres-Id = refl ; pres-⨾ = λ _ _ → refl }
  }
\end{code}
%</make-prod>
The original definition of \AgdaRecord{Monoid} is not the only
way to arrange things. For those familiar with Haskell typeclasses
or Coq's canonical structures, it might also make sense to
privilege the carrier as follows:

%<*monoid-on>
\begin{code}
record MonoidOn (Carrier : Set₀) : Set₀ where
  field
    Id         : Carrier
    _⨾_        : Carrier → Carrier → Carrier
    left-unit  : ∀ {x} → Id ⨾ x ≡ x
    right-unit : ∀ {x} → x ⨾ Id ≡ x
    assoc      : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
\end{code}
%</monoid-on>

\fbox{\textbf{MA: Using name “MonoidOn” instead.}}
If anything, it's more suggestive than Monoid′.

There are definite advantages for doing this. First, we don't need
to bump up the universe level, because now our monoid no longer
\emph{contains} a type, rather it is \emph{parametrized} by a type.
Second, certain mathematical statements are much simpler to state
and prove.  For example, something like
\textit{Given two monoid structures on the same carrier set $S$,
show that $∀ x → e₂ ⨾₂ (x ⨾₁ e₁) ≡ x$}.
\begin{code}
module EasilyFormulated (S : Set) (A B : MonoidOn S) where

  -- C.f., Monoid₁, Monoid₂, Monoid₃, …
  open MonoidOn A renaming (Id to Id₁; _⨾_ to _⨾₁_; right-unit to right-unit₁)
  open MonoidOn B renaming (Id to Id₂; _⨾_ to _⨾₂_; left-unit to left-unit₂)

  claim : ∀ x → Id₂ ⨾₂ (x ⨾₁ Id₁) ≡ x
  claim x = trans left-unit₂ right-unit₁
\end{code}
If we attempt to do the same in the original setting, the
formula $∀ x → e₂ ⨾₂ (x ⨾₁ e₁) ≡ x$ does not even typecheck! We have
to resort so different contortions.  For example, if we forget about
the name $S$, we can instead say:
\begin{code}
module AkwardFormulation
  (A B : Monoid) (ceq : Monoid.Carrier A ≡ Monoid.Carrier B)
  where

  open Monoid₁ A
  open Monoid₂ B

  coe : Carrier₁ → Carrier₂
  coe = subst id ceq

  claim : (x : Carrier₁) → Id₂ ⨾₂ coe (x ⨾₁ Id₁) ≡ coe x
  claim x = trans left-unit₂ (cong coe right-unit₁)
\end{code}
This is not nearly as nice. NB: This isn't a problem specific to Agda,
it is also present in Lean as well. It is a ``feature'' of MLTT.

Here what we want to do is along the lines of
\begin{pseudocode}
derive MonoidOn = hoist sorts
\end{pseudocode}

In the Agda standard library, another variation is used. Here we present
a simplified version, as the actual version (correctly!) takes advantage
of the fact that there is structure on theories as well.

\fbox{\textbf{MA: Does target audiance know what “structure on theories” means; perhaps explain it.}}

\begin{code}
record IsMonoid {Carrier : Set}
                (_⨾_ : Carrier → Carrier → Carrier)
                (Id : Carrier) : Set where
  field
    left-unit  : ∀ {x} → Id ⨾ x ≡ x
    right-unit : ∀ {x} → x ⨾ Id ≡ x
    assoc      : ∀ {x y z} → (x ⨾ y) ⨾ z ≡ x ⨾ (y ⨾ z)
\end{code}

This could be written as:
\begin{pseudocode}
derive IsMonoid = hoist-implicit sorts $
  hoist-expanded operations ''Monoid
\end{pseudocode}

Going back to representing the ``language'' associated to a theory,
we can shift from the labelled-product form of the Signature record
to the labelled-sum form, i.e. an algebraic data type:
\begin{code}
module Closed where

  data CTerm : Set where
    Id  : CTerm
    _⨾_ : CTerm → CTerm → CTerm
\end{code}

Naturally, for \AgdaRecord{Monoid}, this is not particularly interesting,
unlike for \AgdaRecord{SemiRing} (say).
\fbox{\textbf{MA: Squag was mentoned for a reason? }}

Nevertheless, we can still usefully write some generic functions,
such as mapping a closed term from its syntax tree to its
interpretation in that monoid, a generic length function, and
a generic (decidable) equality on the syntax.
\begin{code}
  infix 999 _⟦_⟧

  _⟦_⟧ : (ℳ : Monoid) → CTerm → Monoid.Carrier ℳ
  ℳ ⟦ Id ⟧    = Monoid.Id ℳ
  ℳ ⟦ x ⨾ y ⟧ = ℳ ⟦ x ⟧ ⨾₁ ℳ ⟦ y ⟧ where open Monoid₁ ℳ

  -- Ground terms can only be formed using Id and composition;
  -- whence any interpretation is semantically equivalent to Id.
  boring-semantics : ∀ (ℳ : Monoid) (t : CTerm) → ℳ ⟦ t ⟧ ≡ Monoid.Id ℳ
  boring-semantics ℳ Id = refl
  boring-semantics ℳ (l ⨾ r) = let open Monoid₁ ℳ in
     begin
       ℳ ⟦ l ⨾ r ⟧
     ≡⟨ refl  ⟩
       ℳ ⟦ l ⟧ ⨾₁ ℳ ⟦ r ⟧
     ≡⟨ cong₂ _⨾₁_ (boring-semantics ℳ l) (boring-semantics ℳ r)  ⟩
       Id₁ ⨾₁ Id₁
     ≡⟨ left-unit₁  ⟩
       Id₁
     ∎

  length : CTerm → ℕ
  length Id      = 1
  length (x ⨾ y) = 1 + length x + length y

  data _≈_ : CTerm → CTerm → Set where
    ≈-base : Id ≈ Id
    ≈-step : ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → (a ⨾ b) ≈ (a′ ⨾ b′)
\end{code}

Of course, much more useful is a type that may contain
\emph{free variables}, i.e. open terms.  As we'd like to maintain decidable
equality of our syntax trees, we'll insist that our variables
come from a \emph{decidable setoid}.
\begin{code}
module Open where

  data OTerm (𝒱 : DecSetoid lzero lzero) : Set where
    Var : DecSetoid.Carrier 𝒱 → OTerm 𝒱
    Id  : OTerm 𝒱
    _⨾_ : OTerm 𝒱 → OTerm 𝒱 → OTerm 𝒱
\end{code}
The overall code remains straightforward, but we can illustrate the
interpreter to see the kind of adjustment needed. The attentive
reader will recognize this as a non-trivial \textsf{catamorphism}
for the algebra of open terms over the language of monoids.
\begin{code}
  module Interpret {𝒱 : DecSetoid lzero lzero} (A : Monoid) where

    open DecSetoid 𝒱 renaming (Carrier to V)
    open Monoid₁ A
    open OTerm

    ⟦_⟧_ : OTerm 𝒱 → (V → Carrier₁) → Carrier₁
    ⟦ Var x ⟧ σ = σ x
    ⟦ Id    ⟧ σ = Id₁
    ⟦ l ⨾ r ⟧ σ = (⟦ l ⟧ σ) ⨾₁ (⟦ r ⟧ σ)

    length : OTerm 𝒱 → ℕ
    length (Var _) = 1
    length Id      = 1
    length (x ⨾ y) = 1 + length x + length y
\end{code}
We can use such open terms as part of a generic language of
\emph{formulas}, so that we can then reify the syntax of the
equations too.
\begin{code}
    infix 5 _≃_

    data Formula : Set where
      _≃_ : OTerm 𝒱 → OTerm 𝒱 → Formula

    lhs : Formula → OTerm 𝒱
    lhs (l ≃ _) = l

    rhs : Formula → OTerm 𝒱
    rhs (_ ≃ r) = r
\end{code}
But we can go further and look at the
(dependently typed!) induction principle associated to
\AgdaRecord{OTerm}.
\begin{code}
    induction : (P : OTerm 𝒱 → Set)
              {- Base Cases -}
              → (∀ x → P (Var x))
              → P Id
              {- Inductive step -}
              → (∀ x y → P (x ⨾ y))
              {- Conclusion -}
              → ∀ (y : OTerm 𝒱) → P y
    induction P vars empty ind (Var x) = vars x
    induction P vars empty ind Id      = empty
    induction P vars empty ind (l ⨾ r) = ind l r
\end{code}

For simplicity, let's fix $𝒱$ to be characters.
\begin{code}

  module Example (B : Monoid) where

    import Data.Char as C

    CharSetoid : DecSetoid lzero lzero
    CharSetoid = StrictTotalOrder.decSetoid C.strictTotalOrder

    open Interpret {CharSetoid} B
    OT = OTerm CharSetoid

    left-unit-term : Formula
    left-unit-term = Id ⨾ Var 'x' ≃ Var 'x'

    assoc-term : Formula
    assoc-term = Var 'x' ⨾ (Var 'y' ⨾ Var 'z') ≃ (Var 'x' ⨾ Var 'y') ⨾ Var 'z'

\end{code}

The ``obvious'' idea is then to filter the formulas, and only
use the ones that reduce the length when oriented.  If we bias
things from left-to-right, this gives:
\begin{code}
    reduces : Formula → Set
    reduces F = length (lhs F) > length (rhs F)
\end{code}

\fbox{\textbf{MA: Perhaps mention that this is essentially how Isabelle/Coq/etc do simpl rewriting? }}

\begin{code}
    left-unit-reduces : reduces left-unit-term  -- ≈ “2 ≤ 3”
    left-unit-reduces = s≤s (s≤s z≤n)

    not-assoc-reduces : ¬ (reduces assoc-term)  -- ≈ “6 ≰ 5”
    not-assoc-reduces = λ { (s≤s (s≤s (s≤s (s≤s (s≤s ())))))}
\end{code}
Those proofs are ugly, but automatic. In any case, what they
really allow is to induce a rewriting which preserves meaning
and terminating. It is incomplete!  We need to be smarter to
make it complete (left to another day, as that is not easy).

\fbox{\textbf{MA: Not at all clear how these proofs are “automatic”! }}
Moreover, unclear what goal they accomplish? Why are they interesting?

Let's now turn to forming canonical forms, or forms as simple as possible.
\begin{code}
    simp : OT → OT
    simp (Var x)                 = Var x
    simp Id                      = Id
    simp (Id ⨾ y)                = simp y          {- Identity law -}
    simp (Var x ⨾ y)             = Var x ⨾ simp y
    simp (x@(_ ⨾ _) ⨾ Var y)     = simp x ⨾ Var y
    simp (x@(_ ⨾ _) ⨾ Id)        = simp x           {- Identity law -}
    simp (x@(_ ⨾ _) ⨾ y@(_ ⨾ _)) = simp x ⨾ simp y

\end{code}
Such simplification does not destory semantics:
\begin{code}
    open Monoid₂ B

    coherence : ∀ x σ → ⟦ x ⟧ σ ≡ ⟦ simp x ⟧ σ
    coherence (Var x) σ                 = refl
    coherence Id σ                      = refl
    coherence (Var x ⨾ x₁) σ            = cong (λ z → (σ x) ⨾₂ z) (coherence x₁ σ)
    coherence (Id ⨾ x₁) σ               = trans left-unit₂ (coherence x₁ σ)
    coherence (x@(_ ⨾ _) ⨾ Var x₁) σ    = cong (λ z → z ⨾₂ σ x₁) (coherence x σ)
    coherence (x@(_ ⨾ _) ⨾ Id) σ        = trans right-unit₂ (coherence x σ)
    coherence (x@(_ ⨾ _) ⨾ y@(_ ⨾ _)) σ = cong₂ _⨾₂_ (coherence x σ) (coherence y σ)
\end{code}

In Agda, like in many other languages, we can also be abstract
over representations, much like in ``finally tagless':
\begin{code}
module Tagless where

  record Symantics (rep : Set → Set) (A : Monoid) : Set₁ where
    open Monoid A using (Carrier)
    field
      Id  : rep Carrier
      _⨾_ : rep Carrier → rep Carrier → rep Carrier
\end{code}

\fbox{\textbf{MA: Briefly mention benefit of this approach. }}

We can further choose to internalize the proofs too, as well as add
a generic lifting operator -- though that will only really work for
certain kinds of monoids. Note that Agda allows us to overload field
names, but we must be careful with what we bring into scope when we
work with these.

From here, one can continue and define a \AgdaType{Code} type that
simulates \textsf{metaocaml}'s, and from there to put all things together
to generate a \textbf{partial evaluator} for the term language.

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

Slightly realated investigation.

\begin{spec}
-- The following may be easier to state not as “𝒮.Carrier ≈ ℳ.Carrier ≈ 𝟙 → C ≈ 𝟙”
-- but as “SquagOn C → MonoidOn C → C ≈ 𝟙”
--
module on-vs-has where

  open import Function.Inverse using () renaming (_↔_ to _≅_)

  data 𝟙 : Set where ★ : 𝟙

  trivial-intersection : ∀ (C : Set) (S : Squag) (M : Monoid)
                           (let module 𝒮 = Squag S)
                           (let module ℳ = Monoid M)
                         → 𝒮.Carrier ≡ ℳ.Carrier → ℳ.Carrier ≡ C
                         → C ≅ 𝟙
  trivial-intersection .(Monoid.Carrier q)
    (sq .(Monoid.Carrier q) _⨾_ idempotent commutative antiAbsorbent)
    q refl refl =
      let
        𝒾 = Monoid.Id q

        all-Id : ∀ (x : Monoid.Carrier q) → Monoid.Id q ≡ x
        all-Id x = begin
                     𝒾
                   ≡⟨ sym (antiAbsorbent _ _ )  ⟩
                     x ⨾ (x ⨾ 𝒾)
                   ≡⟨ cong (x ⨾_) {!Oh! The Squag ⨾ and Monoid ⨾ may be completely different. Neato. !} ⟩
                     x ⨾ x
                   ≡⟨ idempotent _  ⟩
                     x
                   ∎
      in
      record { to = record { _⟨$⟩_ = λ _ → ★ ; cong = λ _ → refl  }
                         ; from = record { _⟨$⟩_ = λ _ → Monoid.Id q ; cong = λ _ → refl }
                         ; inverse-of = record { left-inverse-of = all-Id
                                               ; right-inverse-of = λ{ ★ → refl}
                                               }
                         }
\end{spec}
