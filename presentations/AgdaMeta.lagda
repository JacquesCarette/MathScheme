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

record Monoid-Signature : Set₁ where
  field
    m : Set₀
    e : m
    _*_ : m → m → m

record SubMonoid (A : Monoid) : Set₁ where
  module a = Monoid A
  field
     B⊂A : Pred a.m lzero
     B⊂A-contr : ∀ {x : a.m} → {p q : B⊂A x} → p ≡ q
     e∈ : a.e ∈ B⊂A
     closed : ∀ {x y : a.m} → B⊂A x → B⊂A y → B⊂A (x a.* y)

-- dependently typed cong₂
cong₂D  :  {a b c : Level} {A : Set a} {B : A → Set b} {C : Set c} (f : (x : A) → B x → C)
          →  {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂}
          →  (x₁≡x₂ : x₁ ≡ x₂) → y₁ ≡ subst B (sym x₁≡x₂) y₂ → f x₁ y₁ ≡ f x₂ y₂
cong₂D f refl refl = refl

SubM⇒M : {A : Monoid} → SubMonoid A → Monoid
SubM⇒M {mon m e _*_ left-unit right-unit assoc} record { B⊂A = B⊂A ; B⊂A-contr = contr; e∈ = e∈ ; closed = closed } =
  mon m′ (e , e∈) _op_ left-unit′ (λ x → cong₂D _,_ (right-unit (proj₁ x)) contr)
    (λ x y z → cong₂D _,_ (assoc (proj₁ x) (proj₁ y) (proj₁ z)) contr)
  where
    m′ : Set₀
    m′ = Σ m B⊂A
    _op_ : m′ → m′ → m′
    (a , p) op (b , q) = (a * b , closed p q )
    left-unit′ : (x : m′) → ((e , e∈) op x) ≡ x
    left-unit′ (a , a⊂ ) = cong₂D _,_ (left-unit a) contr

record Monoid-Homomorphism (A B : Monoid) : Set₁ where
  open Monoid
  module a = Monoid A
  module b = Monoid B
  field
    f : a.m → b.m
    pres-e : f a.e ≡ b.e
    pres-* : (x y : a.m) → f (x a.* y) ≡ (f x) b.* (f y)

record Monoid-Identity-Homomorphism (A : Monoid) : Set₁ where
  open Monoid
  module a = Monoid A
  field
    f : a.m → a.m
    equivalence : ∀ x → f x ≡ x
    hom : (x y : a.m) → f (x a.* y) ≡ (f x) a.* (f y)

record Monoid-Homomorphism-Equality {A B : Monoid} (F G : Monoid-Homomorphism A B) : Set₁ where
  module f = Monoid-Homomorphism F
  module g = Monoid-Homomorphism G
  field
    F≡G : ∀ a → f.f a ≡ g.f a

record Monoid-Homomorphism-Kernel {A B : Monoid} (F : Monoid-Homomorphism A B) : Set₁ where
  module a = Monoid A
  module b = Monoid B
  module f = Monoid-Homomorphism F
  field
    cond : Σ (a.m × a.m) λ { (x , y) → f.f x ≡ f.f y }

record Monoid-Isomorphism (A B : Monoid) : Set₁ where
  open Monoid
  open Monoid-Homomorphism
  field
    A⇒B : Monoid-Homomorphism A B
    g : m B → m A
    f∘g≡id : ∀ x → ((f A⇒B) F.∘ g) x ≡ F.id x
    g∘f≡id : ∀ x → (g F.∘ (f A⇒B)) x ≡ F.id x

record Monoid-Endomorphism (A : Monoid) : Set₁ where
   open Monoid
   open Monoid-Homomorphism
   field
     A⇒A : Monoid-Homomorphism A A

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
     Proj1 : Monoid-Homomorphism ProdM A
     Proj2 : Monoid-Homomorphism ProdM B

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
