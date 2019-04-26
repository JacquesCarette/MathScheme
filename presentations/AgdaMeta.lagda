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
open import Function as F
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
-- Yasmine, can you add Squag here please?
\end{code}
First, there is a general notion of homomorphism between
theories: a mapping from the carrier of one theory to
the other, that \emph{preserves} each of the operations:
\begin{code}
module Derived where
record Homomorphism (A B : Monoid) : Set₁ where
  open Monoid
  module a = Monoid A
  module b = Monoid B
  field
    f : a.m → b.m
    pres-e : f a.e ≡ b.e
    pres-* : ∀ x y → f (x a.* y) ≡ (f x) b.* (f y)
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

Observe how each item (field) of \AgdaRecord{Homomorphism}
comes from one of \AgdaRecord{Signature}. This generalizes
``on the nose'' for other theories.

\begin{code}
record Monoid-Homomorphism-Equality {A B : Monoid} (F G : Homomorphism A B) : Set₁ where
  module f = Homomorphism F
  module g = Homomorphism G
  field
    F≡G : ∀ a → f.f a ≡ g.f a

record Monoid-Homomorphism-Kernel {A B : Monoid} (F : Homomorphism A B) : Set₁ where
  module a = Monoid A
  module b = Monoid B
  module f = Homomorphism F
  field
    cond : Σ (a.m × a.m) λ { (x , y) → f.f x ≡ f.f y }

record Monoid-Isomorphism (A B : Monoid) : Set₁ where
  open Monoid
  open Homomorphism
  field
    A⇒B : Homomorphism A B
    g : m B → m A
    f∘g≡id : ∀ x → ((f A⇒B) F.∘ g) x ≡ F.id x
    g∘f≡id : ∀ x → (g F.∘ (f A⇒B)) x ≡ F.id x

record Monoid-Endomorphism (A : Monoid) : Set₁ where
   open Monoid
   open Homomorphism
   field
     A⇒A : Homomorphism A A

record Monoid-Automorphism (A : Monoid) : Set₁ where
   open Monoid
   open Monoid-Isomorphism
   field
     A⇒A : Monoid-Isomorphism A A

foo : {A B : Set} → {ab : A × B} → {a : A} → {b : B} → proj₁ ab ≡ a → proj₂ ab ≡ b → ab ≡ (a , b)
foo refl refl = refl

foo2 : {A B : Set} → A × B → A
foo2 (a , b) = a

record _×M_ (A B : Monoid) : Set₂ where
   constructor prod
   field
     ProdM : Monoid
     Proj1 : Homomorphism ProdM A
     Proj2 : Homomorphism ProdM B

Cartesian-Product : (A : Monoid) → (B : Monoid) → A ×M B
Cartesian-Product (mon m e _*_ left-unit right-unit assoc) (mon m₁ e₁ _*₁_ left-unit₁ right-unit₁ assoc₁) =
   prod product (record { f = prod1 ; pres-e = refl ; pres-* = assoc1 }) (record { f = prod2 ; pres-e = refl ; pres-* = assoc2 })
     where
       mprod = (m × m₁)
       eprod = (e , e₁)
       _*₂_ = λ {(a , b) (c , d) → (a * c , b *₁ d)}
       left-unit₂ : (x : mprod) → eprod *₂ x ≡ x
       left-unit₂ (a , b) = cong₂ _,_ (left-unit a) (left-unit₁ b)
       right-unit₂ : (x : mprod) → x *₂ eprod ≡ x
       right-unit₂ (a , b) = cong₂ _,_ (right-unit a) (right-unit₁ b)
       assoc₂ : (x y z : mprod) → (x *₂ y) *₂ z ≡ x *₂ (y *₂ z)
       assoc₂ (a , b) (c , d) (m , n) = cong₂ _,_ (assoc a c m) (assoc₁ b d n)
       product = (mon mprod eprod _*₂_  left-unit₂ right-unit₂ assoc₂)
       prod1 : mprod → m
       prod1 (a , b) = a
       prod2 : mprod → m₁
       prod2 (a , b) = b
       assoc1 : (x y : mprod) → prod1 (x *₂ y) ≡ (prod1 x) * (prod1 y)
       assoc1 (a , b) (c , d) = refl
       assoc2 : (x y : mprod) → prod2 (x *₂ y) ≡ (prod2 x) *₁ (prod2 y)
       assoc2 (a , b) (c , d) = refl

-- finally tagless representation of a theory
record Lift_Monoid (rep : Set₀ → Set₀) (A : Monoid) : Set₁ where
  module a = Monoid A
  field
    e′ : rep a.m
    _*′_ : rep a.m → rep a.m → rep a.m

data Monoid-Closed-Term : Set where
  e : Monoid-Closed-Term
  _*_ : Monoid-Closed-Term → Monoid-Closed-Term → Monoid-Closed-Term

data Monoid-Open-Term (V : Setoid lzero lzero) : Set where
  v : Setoid.Carrier V → Monoid-Open-Term V
  e : Monoid-Open-Term V
  _*_ : Monoid-Open-Term V → Monoid-Open-Term V → Monoid-Open-Term V

-- evaluation : mapping a closed term from syntax to interpretation
_⟦_⟧ : (A : Monoid) → Monoid-Closed-Term → Monoid.m A
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
