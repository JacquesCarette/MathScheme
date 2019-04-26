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

open import Relation.Unary
open import Relation.Binary
import Function as F
open F using (id; _∘_)
open import Agda.Primitive
open import Data.Product
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning
\end{code}
}

Our primary example will be Monoid:
\begin{code}
record Monoid : Set₁ where
  constructor mon
  field
    m : Set₀
    e : m
    _*_ : m → m → m
    left-unit : ∀ x → e * x ≡ x
    right-unit : ∀ x → x * e ≡ x
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
the great usefullness of the common core. The above coincides
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
    f : a.m → b.m
    pres-e : f a.e ≡ b.e
    pres-* : ∀ x y → f (x a.* y) ≡ (f x) b.* (f y)

infixr 20 _$_
_$_ : {A B : Monoid} → Hom A B → (Monoid.m A → Monoid.m B)
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
confusion.

Observe how each item (field) of \AgdaRecord{Hom}
comes from one of \AgdaRecord{Signature}. This generalizes
``on the nose'' for other theories.

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
    g : m B → m A
    f∘g≡id : (f A⇒B ∘ g) ∼ id
    g∘f≡id : (g ∘ f A⇒B) ∼ id

  inv-is-Hom : Hom B A
  inv-is-Hom = record
    { f = g
    ; pres-e = trans (sym (cong g (pres-e A⇒B))) (g∘f≡id (e A))
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
    x : m A
    y : m A
    cond : F $ x ≡ F $ y
\end{code}

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

In Agda, like in many other languages, we can also be abstract
over representations, much like in ``finally tagless':
\begin{code}
record Symantics (rep : Set₀ → Set₀) (A : Monoid) : Set₁ where
  a = Monoid.m A
  field
    e : rep a
    _*_ : rep a → rep a → rep a
\end{code}

We can further choose to internalize the proofs too, as well as add
a generic lifting operator -- though that will only really work for
certain kinds of monoids. Note that Agda allows us to overload field
names, but we must be careful with what we bring into scope when we
work with these.

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
  open Monoid M₁ renaming (e to e₁; _*_ to _*₁_; right-unit to ru; m to m₁)
  open Monoid M₂ renaming (e to e₂; _*_ to _*₂_; left-unit to lu; m to m₂)
  postulate
    eq : m₁ ≡ m₂
  coe : {A B : Set} → A ≡ B → (a : A) → B
  coe refl a = a
  stat : (x : m₁) → e₂ *₂ (coe eq (x *₁ e₁)) ≡ coe eq x
  stat x = trans (lu _) (cong (coe eq) (ru x))
\end{code}
which is not nearly as nice. NB: this isn't a problem specific to Agda,
it is also present in Lean as well. It is a ``feature'' of MLTT.

Going back to representing the ``language'' associated to a theory
\begin{code}
data CTerm : Set where
  e : CTerm
  _*_ : CTerm → CTerm → CTerm

data Monoid-Open-Term (V : Setoid lzero lzero) : Set where
  v : Setoid.Carrier V → Monoid-Open-Term V
  e : Monoid-Open-Term V
  _*_ : Monoid-Open-Term V → Monoid-Open-Term V → Monoid-Open-Term V

-- evaluation : mapping a closed term from syntax to interpretation
_⟦_⟧ : (A : Monoid) → CTerm → Monoid.m A
A ⟦ e ⟧ = Monoid.e A
A ⟦ x * y ⟧ = let _op_ = Monoid._*_ A in (A ⟦ x ⟧) op (A ⟦ y ⟧)

-- record Monoid_Signature_Expansion (A : Monoid_Signature) : Set₁ where
--   open Monoid_Signature
--   module a = Monoid_Signature A
--   field
--     b : Monoid_Signature
--      subset : a.m ⊆ b.m
--      func_eq : ∀ f

\end{code}
