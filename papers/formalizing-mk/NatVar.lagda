\AgdaHide{
Showing that ℕ has decidable equality (and thus can be used as a set
of variables).  Also build ℕX which is ℕ augmented with variables.

\begin{code}
module NatVar where

open import Level renaming (zero to lzero) hiding (suc)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Equiv
open import Data.Empty using (⊥)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; isEquivalence)
open import Relation.Binary using (DecSetoid)

private
  DT : Set₁
  DT = DecSetoid lzero lzero
  
ℕS : DT
ℕS = record
  { Carrier = ℕ
  ; _≈_ = _≡_
  ; isDecEquivalence = record
    { isEquivalence = isEquivalence
    ; _≟_ = _≟_ } }
\end{code}
}

\begin{code}
data ℕX (Var : Set₀) : Set₀ where
  z : ℕX Var
  s : ℕX Var → ℕX Var
  v : Var → ℕX Var
\end{code}

\AgdaHide{
\begin{code}
ℕ⊥≃ℕ : ℕX ⊥ ≃ ℕ
ℕ⊥≃ℕ = qeq f g f∘g∼id g∘f∼id
  where
    f : ℕX ⊥ → ℕ
    f z = 0
    f (s x) = suc (f x)
    f (v ())
    g : ℕ → ℕX ⊥
    g zero = z
    g (suc n) = s (g n)
    f∘g∼id : f ∘ g ∼ id
    f∘g∼id zero = refl
    f∘g∼id (suc x) = cong suc (f∘g∼id x)
    g∘f∼id : g ∘ f ∼ id
    g∘f∼id z = refl
    g∘f∼id (s x) = cong s (g∘f∼id x)
    g∘f∼id (v ())
\end{code}
}
