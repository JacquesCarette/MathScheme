\AgdaHide{
\begin{code}
-- The encoding uses the 'local method'.
module T1 where

open import Relation.Binary using (DecSetoid)
open DecSetoid using (Carrier)
open import Level using () renaming (zero to lzero)

-- we use ⊥, ¬ and ≡ from the 'meta' logic
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
open import Data.Nat using (ℕ; suc) -- instead of defining our own
  -- isomorphic copy
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([_])
open import Data.Bool using (false)

-- we will eventually need this
open import Language
open import NatVar

private
  DT = DecSetoid lzero lzero
\end{code}
}

\begin{code}

record BT₁ : Set₁ where
  field
    nat : Set₀
    Z : nat
    S : nat → nat
    S≠Z : ∀ x → ¬ (S x ≡ Z)
    inj : ∀ x y → S x ≡ S y → x ≡ y

  One : nat
  One = S Z
\end{code} 

For simplicity, we will take the built-in type $\mathbb{N}$,
defined as an inductive type, as the \emph{syntax} for natural
numbers, which is also the syntax associated to the theory
\AgdaRecord{BT₁}.  Whereas in {\churchuqe} there is a global evaluation, here
we also need to define evaluation explicitly (a subscript is used to
indicate which theory it belongs to).\\

\begin{code}
  ⟦_⟧₁ : ℕ → nat
  ⟦ 0 ⟧₁ = Z
  ⟦ suc x ⟧₁ = S ⟦ x ⟧₁
\end{code}
\AgdaHide{
\begin{code}
  -- and some coherence theorems:
  pres-S≠Z : (x : ℕ) → ¬ ⟦ suc x ⟧₁ ≡ ⟦ 0 ⟧₁
  pres-S≠Z x = S≠Z ⟦ x ⟧₁

  pres-inj : (x y : ℕ) → S ⟦ x ⟧₁ ≡ S ⟦ y ⟧₁ → ⟦ x ⟧₁ ≡ ⟦ y ⟧₁
  pres-inj x y pf = inj ⟦ x ⟧₁ ⟦ y ⟧₁ pf
\end{code}
}
The accompanying code furthermore proves some basic coherence
theorems which are elided here.  We make two further definitions
(\AgdaRecord{GroundLanguage} describing some language features,
and \AgdaModule{FOL} as our definition of first order logic)
which will be explained in more detail on the next page.

\begin{code}
  nat-lang : GroundLanguage nat
  nat-lang = record { Lang = λ X → ℕX (Carrier X)
                    ; value = λ {V} → val {V} }
    where
      val : {V : DT} → ℕX (Carrier V) → (Carrier V → nat) → nat
      val      z    env = Z
      val {V} (s e) env = S (val {V} e env)
      val     (v x) env = env x
      
  module fo₁ = FOL nat-lang
\end{code}

We can also demonstrate that the natural numbers are a model:\\

\begin{code}
ℕ-is-T1 : BT₁
ℕ-is-T1 = record { nat = ℕ ; Z = 0 ; S = suc
  ; S≠Z = λ x → λ () ; inj = λ { x .x refl → refl } }
\end{code}

\AgdaHide{
\begin{code}

-- inverse of the type of sub-term of ℕX
SubTermType : {V : DT} → ℕX (Carrier V) → Set₀
SubTermType {_} z = ⊥
SubTermType {V} (s x) = ℕX (Carrier V)
SubTermType {V} (v x) = Carrier V

-- paths in a ℕX
data Path {V : DT} : (e : ℕX (Carrier V)) → SubTermType {V} e → Set₀ where
  sp : (x : ℕX (Carrier V)) → Path (s x) x
  vp : (x : Carrier V) → Path (v x) x
\end{code}
}
