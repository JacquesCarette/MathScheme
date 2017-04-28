This defines the tools needed to do the equivalent of definite description in
MLTT.  

\begin{code}
module DefiniteDescr where
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ;_×_)
\end{code}
  
\noindent Normal contractability of a type

\begin{code}
isContr : Set₀ → Set₀
isContr A = Σ A (λ a → ∀ b → a ≡ b)
\end{code}

We now "expand out" that definition when A is a Σ-type
with the first type that of a 2-argument function, and the
second is a predicate (and thus automatically contractible).
We could elide the second part via proof irrelevance.

\begin{code}
isContr₂ : (B : Set₀) → let bin = B → B → B in (bin → Set₀) → Set₀
isContr₂ A P =
  let bin = A → A → A in
  Σ bin (λ f → P f ×
               (∀ (g : A → A → A) → P g → ∀ a b → f a b ≡ g a b) ×
               (∀ (pf₁ pf₂ : P f) → pf₁ ≡ pf₂))
\end{code}
