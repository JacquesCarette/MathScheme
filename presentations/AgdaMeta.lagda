This is the (partial) story of encoding certain kinds of knowledge
in Agda. More importantly, the story of \textbf{deriving} a lot
of knowledge \emph{mechanically}.

This story will be told through examples, shown in what a human would
traditionally write without tool support. We do have a couple of
prototypes (one in ocaml, the other in emacs lisp & common lisp)
that automates this, but they are both syntactically awkward and
thus not as well suited for clear communication.

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
\begin{code}
record Monoid : Set₁ where
  constructor mon
  field
    Carrier : Set₀
    Id : Carrier
    _*_ : Carrier → Carrier → Carrier
    left-unit : ∀ x → Id * x ≡ x
    right-unit : ∀ x → x * Id ≡ x
    assoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
\end{code}

A Monoid is over a type, has a distinguished point in that type
and a (total) binary operation over that type. There are also three
axioms: that the point is a left and right unit for the operation,
and that the operation is associative. Note that we choose to use
propositional equality for the axioms.

In general, we will here consider particular kinds of \emph{theories},
for which we know how to manipulate definitions. These are not
particularly restrictive as most theories from traditional Algebra
fit.  Specifically, we'll look closely at
\emph{1-sorted finitary equational theories}, meaning that
we have
\begin{itemize}
\item a single carrier set (1-sorted)
\item we declare finitely many symbols, denoting operations,
each with arity $≥ 0$
\item axioms of the form
\[ ∀ x y z. term ≡ term \]
\end{itemize}
Naturally, each one of these can be generalized, but each such
generalization brings in non-trivial difficulties that obscure
the great usefullness of the common core.

For later convenience, let us call each kind of definition
\textbf{sorts}, \textbf{operations} and \textbf{equations}
respectively.

The above coincides
exactly with \textsf{Universal Algebra} as initiated by
Alfred North Whitehead in his 1898 book \textit{A Treatise of Universal
Algebra}.

Our motto here:

\begin{centering}
\Large Make easy things easy
\end{centering}

A lot of CS research focuses on the other end of the spectrum,
perhaps aptly phrased as \emph{Make hard things feasible}. Our aim
is to create tools for humans to \emph{automate drudgery} so that
they may spend more time on aspects where creativity and insight
are actually needed.

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
    s : Set₀
    _*_ : s → s → s
    idempotent : ∀ x → x * x ≡ x
    commutative : ∀ x y → x * y ≡ y * x
    antiAbsorbent : ∀ x y → x * (x * y) ≡ y
\end{code}

First, there is a general notion of homomorphism between
theories: a mapping from the carrier of one theory to
the other, that \emph{preserves} each of the operations. It is
customary to shorten the name to $\AgdaRecord{Hom}$.
\begin{code}
module Derived where
record Hom (A B : Monoid) : Set₁ where
  open Monoid
  module a = Monoid A
  module b = Monoid B
  field
    f : a.Carrier → b.Carrier
    pres-e : f a.Id ≡ b.Id
    pres-* : ∀ x y → f (x a.* y) ≡ (f x) b.* (f y)

infixr 20 _$_
_$_ : {A B : Monoid} → Hom A B → (Monoid.Carrier A → Monoid.Carrier B)
H $ x = Hom.f H x
\end{code}

The above makes fundamental use of what is often called
(in the Universal Algebra literature) the \emph{signature}
of the theory:
\begin{code}
record Signature : Set₁ where
  field
    m : Set₀
    e : m
    _*_ : m → m → m
\end{code}
Of course, in a dependently-typed setting, Monoid itself is
also called a signature, which can unfortunately lead to
confusion. What is important to notice here is that it ought to
be possible to write the follow meta-program:

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

For example, we can look at what equality of two
homomorphisms could be. So we compute the ``signature''
of \AgdaRecord{Hom} and insist that each field be
appropritely related.  In particular, for functions,
this is going to be pointwise:

\begin{code}
_∼_ : {A B : Set} (f g : A → B) → Set
f ∼ g = ∀ a → f a ≡ g a

record Hom-Equality {A B : Monoid} (F G : Hom A B) : Set₁ where
  field
    F≡G : Hom.f F ∼ Hom.f G
\end{code}

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
    f∘g≡id : (f A⇒B ∘ g) ∼ id
    g∘f≡id : (g ∘ f A⇒B) ∼ id

  inv-is-Hom : Hom B A
  inv-is-Hom = record
    { f = g
    ; pres-e = trans (sym (cong g (pres-e A⇒B))) (g∘f≡id (Id A))
    ; pres-* = λ x y →  trans (cong g (sym (cong₂ (_*_ B) (f∘g≡id x) (f∘g≡id y))))
               (trans (cong g (sym (pres-* A⇒B (g x) (g y))))
               (g∘f≡id _))
    }
\end{code}

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
\begin{code}
record Kernel {A B : Monoid} (F : Hom A B) : Set₁ where
  open Monoid
  field
    x : Carrier A
    y : Carrier A
    cond : F $ x ≡ F $ y
\end{code}
\AgdaRecord{Kernel} is essentially generic, and can be derived
as a template -- unlike previous definitions, which really do need
simple but ``real'' programs to be run on the representations.

It is then possible to prove (generically) that this
induces an equivalence relation (on $A$) which is furthermore
a congruence, which means that this can be used, at least in a
classical setting, to form quotients.

Cartesian products also exist generically.
\begin{code}
record _×M_ (A B : Monoid) : Set₂ where
   constructor prod
   field
     ProdM : Monoid
     Proj1 : Hom ProdM A
     Proj2 : Hom ProdM B

Cartesian-Product : (A : Monoid) → (B : Monoid) → A ×M B
Cartesian-Product
  (mon m e _*_ left-unit right-unit assoc)
  (mon m₁ e₁ _*₁_ left-unit₁ right-unit₁ assoc₁) =
   prod product (record { f = proj₁ ; pres-e = refl ; pres-* = pres-* })
                (record { f = proj₂ ; pres-e = refl ; pres-* = pres-*₁ })
     where
       e₂ = (e , e₁)
       _*₂_ = λ {(a , b) (c , d) → (a * c , b *₁ d)}
       left-unit₂ : ∀ x → e₂ *₂ x ≡ x
       left-unit₂ (a , b) = cong₂ _,_ (left-unit a) (left-unit₁ b)
       right-unit₂ : ∀ x → x *₂ e₂ ≡ x
       right-unit₂ (a , b) = cong₂ _,_ (right-unit a) (right-unit₁ b)
       assoc₂ : ∀ x y z → (x *₂ y) *₂ z ≡ x *₂ (y *₂ z)
       assoc₂ (a , b) (c , d) (m , n) = cong₂ _,_ (assoc a c m) (assoc₁ b d n)
       product = (mon (m × m₁) e₂ _*₂_  left-unit₂ right-unit₂ assoc₂)

       pres-* : ∀ x y → proj₁ (x *₂ y) ≡ (proj₁ x) * (proj₁ y)
       pres-* (a , b) (c , d) = refl
       pres-*₁ : ∀ x y → proj₂ (x *₂ y) ≡ (proj₂ x) *₁ (proj₂ y)
       pres-*₁ (a , b) (c , d) = refl
\end{code}

The original definition of \AgdaRecord{Monoid} is not the only
way to arrange things. For those familiar with Haskell typeclasses
or Coq's canonical structures, it might also make sense to
priviledge the carrier as follows:

\begin{code}
record Monoid′ (A : Set₀) : Set₀ where
  field
    e : A
    _*_ : A → A → A
    left-unit : ∀ x → e * x ≡ x
    right-unit : ∀ x → x * e ≡ x
    assoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
\end{code}

There are definite advantages for doing this. First, we don't need
to bump up the universe level, because now our monoid no longer
\emph{contains} a type, rather it is \emph{parametrized} by a type.
Second, certain mathematical statements are much simpler to state
and prove.  For example, something like
\textit{Given two monoid structures on the same carrier set $S$,
show that $∀ x → e₂ *₂ (x *₁ e₁) ≡ x$}.
\begin{code}
module Try₁ where
  postulate
    S : Set
    M₁ M₂ : Monoid′ S
  open Monoid′ M₁ renaming (e to e₁; _*_ to _*₁_; right-unit to ru)
  open Monoid′ M₂ renaming (e to e₂; _*_ to _*₂_; left-unit to lu)
  stat : ∀ x → e₂ *₂ (x *₁ e₁) ≡ x
  stat x = trans (lu _) (ru x)
\end{code}
If we attempt to do the same in the original setting, the
formula $∀ x → e₂ *₂ (x *₁ e₁) ≡ x$ does not even typecheck! We have
to resort so different contortions.  For example, if we forget about
the name $S$, we can instead say
\begin{code}
module Try₂ where
  postulate
    M₁ M₂ : Monoid
  open Monoid M₁ renaming (Id to e₁; _*_ to _*₁_; right-unit to ru; Carrier to Carrier₁)
  open Monoid M₂ renaming (Id to e₂; _*_ to _*₂_; left-unit to lu;  Carrier to Carrier₂)
  postulate
    eq : Carrier₁ ≡ Carrier₂
  coe : {A B : Set} → A ≡ B → (a : A) → B
  coe refl a = a
  stat : (x : Carrier₁) → e₂ *₂ (coe eq (x *₁ e₁)) ≡ coe eq x
  stat x = trans (lu _) (cong (coe eq) (ru x))
\end{code}
which is not nearly as nice. NB: this isn't a problem specific to Agda,
it is also present in Lean as well. It is a ``feature'' of MLTT.

Here what we want to do is along the lines of
\begin{pseudocode}
derive Monoid′ = hoist sorts
\end{pseudocode}
In the Agda standard library, another variation is used. Here we present
a simplified version, as the actual version (correctly!) takes advantage
of the fact that there is structure on theories as well.
\begin{code}
record IsMonoid {A : Set} (_*_ : A → A → A) (e : A) : Set where
  field
    left-unit : ∀ x → e * x ≡ x
    right-unit : ∀ x → x * e ≡ x
    assoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
\end{code}

This could be written as
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
    e : CTerm
    _*_ : CTerm → CTerm → CTerm
\end{code}

Naturally, for \AgdaRecord{Monoid}, this is not particularly interesting,
unlike for \AgdaRecord{SemiRing} (say).

Nevertheless, we can still usefully write some generic functions,
such as mapping a closed term from its syntax tree to its
interpretation in that monoid, a generic length function, and
a generic (decidable) equality on the syntax.
\begin{code}
  _⟦_⟧ : (A : Monoid) → CTerm → Monoid.Carrier A
  A ⟦ e ⟧ = Monoid.Id A
  A ⟦ x * y ⟧ = let _++_ = Monoid._*_ A in (A ⟦ x ⟧) ++ (A ⟦ y ⟧)

  length : CTerm → ℕ
  length e = 1
  length (x * y) = 1 + length x + length y

  _≈CT_ : Rel CTerm lzero
  e ≈CT e = ⊤
  e ≈CT (b * b₁) = ⊥
  (a * a₁) ≈CT e = ⊥
  (a * a₁) ≈CT (b * b₁) = a ≈CT b × a₁ ≈CT b₁
\end{code}

Of course, much more useful is a type that may contain
\emph{free variables}, i.e. open terms.  As we'd like to maintain decidable
equality of our syntax trees, we'll insist that our variables
come from a \emph{decidable setoid}.
\begin{code}
module Open where
  data OTerm (V : DecSetoid lzero lzero) : Set where
    v : DecSetoid.Carrier V → OTerm V
    e : OTerm V
    _*_ : OTerm V → OTerm V → OTerm V
\end{code}
The overall code remains straightforward, but we can illustrate the
interpreter to see the kind of adjustment needed. The attentive
reader will recognize this as a non-trivial \textsf{catamorphism}
for the algebra of open terms over the language of monoids.
\begin{code}
  module Interpret {V : DecSetoid lzero lzero} (A : Monoid) where
    open DecSetoid V renaming (Carrier to c)
    open Monoid A renaming (Carrier to a; Id to zero; _*_ to _*₀_)
    open OTerm
    ⟦_⟧_ : OTerm V → (c → a) → a
    ⟦ v x ⟧ σ = σ x
    ⟦ e ⟧ σ = zero
    ⟦ t * t₁ ⟧ σ = (⟦ t ⟧ σ) *₀ (⟦ t₁ ⟧ σ)

    length : OTerm V → ℕ
    length (v _) = 1
    length e = 1
    length (x * y) = 1 + length x + length y
\end{code}
We can use such open terms as part of a generic language of
\emph{formulas}, so that we can then reify the syntax of the
equations too.
\begin{code}
    infix 5 _≃_
    data Formula : Set where
      _≃_ : OTerm V → OTerm V → Formula
    lhs : Formula → OTerm V
    lhs (a ≃ _) = a
    rhs : Formula → OTerm V
    rhs (_ ≃ b) = b
\end{code}
But we can go further and look at the
(dependently typed!) induction principle associated to
\AgdaRecord{OTerm}.
\begin{code}
    induction : (P : OTerm V → Set) → (∀ (x : c) → P (v x)) → P e
      → (∀ x y → P (x * y)) → ∀ (y : OTerm V) → P y
    induction P vars zer pr (v x)    = vars x
    induction P vars zer pr e        = zer
    induction P vars zer pr (t * t₁) = pr t t₁
\end{code}

For simplicity, let's fix $V$ to be characters.
\begin{code}
  module Example (B : Monoid) where
    import Data.Char as C
    CharSetoid : DecSetoid lzero lzero
    CharSetoid = StrictTotalOrder.decSetoid C.strictTotalOrder
    open Interpret {CharSetoid} B
    OT = OTerm CharSetoid

    left-unit-term : Formula
    left-unit-term = e * v 'x' ≃ v 'x'
    assoc-term : Formula
    assoc-term = v 'x' * (v 'y' * v 'z') ≃ (v 'x' * v 'y') * v 'z'
\end{code}

The ``obvious'' idea is then to filter the formulas, and only
use the ones that reduce the length when oriented.  If we bias
things from left-to-right, this gives:
\begin{code}
    reduces : Formula → Set
    reduces F = length (lhs F) > length (rhs F)

    left-unit-reduces : reduces left-unit-term
    left-unit-reduces = s≤s (s≤s z≤n)

    not-assoc-reduces : ¬ (reduces assoc-term)
    not-assoc-reduces = λ { (s≤s (s≤s (s≤s (s≤s (s≤s ())))))}
\end{code}
Those proofs are ugly, but automatic. In any case, what they
really allow is to induce a rewriting which preserves meaning
and terminating. It is incomplete!  We need to be smarter to
make it complete (left to another day, as that is not easy).

\begin{code}
    simp : OT → OT
    simp (v x) = v x
    simp e = e
    simp (e * y) = simp y
    simp (v x * y) = v x * simp y
    simp (x@(_ * _) * v y) = simp x * v y
    simp (x@(_ * _) * e) = simp x
    simp (x@(_ * _) * y@(_ * _)) = simp x * simp y

    _++_ = Monoid._*_ B
    coherence : ∀ x σ → ⟦ x ⟧ σ ≡ ⟦ simp x ⟧ σ
    coherence (v x) σ = refl
    coherence e σ = refl
    coherence (v x * x₁) σ = cong (λ z → (σ x) ++ z) (coherence x₁ σ)
    coherence (e * x₁) σ = trans (Monoid.left-unit B _) (coherence x₁ σ)
    coherence (x@(_ * _) * v x₁) σ = cong (λ z → z ++ σ x₁) (coherence x σ)
    coherence (x@(_ * _) * e) σ = trans (Monoid.right-unit B _) (coherence x σ)
    coherence (x@(_ * _) * y@(_ * _)) σ = cong₂ _++_ (coherence x σ) (coherence y σ)
\end{code}

In Agda, like in many other languages, we can also be abstract
over representations, much like in ``finally tagless':
\begin{code}
module Tagless where
  record Symantics (rep : Set₀ → Set₀) (A : Monoid) : Set₁ where
    a = Monoid.Carrier A
    field
      e : rep a
      _*_ : rep a → rep a → rep a
\end{code}

We can further choose to internalize the proofs too, as well as add
a generic lifting operator -- though that will only really work for
certain kinds of monoids. Note that Agda allows us to overload field
names, but we must be careful with what we bring into scope when we
work with these.

From here, one can continue and define a \AgdaType{Code} type that
simulates \textsf{metaocaml}'s, and from there to put all things together
to generate a \textbf{partial evaluator} for the term language.
