\begin{code}
module T8 where
open import DefiniteDescr using (isContr₂)

open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ; proj₁; _×_)

record BT₈ : Set₁ where
  field
    ι : Set₀
    ze : ι
    S : ι → ι
    S≠Z : ∀ x → ¬ (S x ≡ ze)
    inj : ∀ x y → S x ≡ S y → x ≡ y
    induct : (p : ι → Set₀) → p ze → (∀ x → p x → p (S x)) → (∀ y → p y)

  bin : Set₀
  bin = ι → ι → ι

  +-pred : bin → Set₀
  +-pred f = (∀ x → f x ze ≡ x) ×
             (∀ x y → f x (S y) ≡ S (f x y))

  field
    +-uniq : isContr₂ ι +-pred

  _+_ : bin
  _+_ = proj₁ +-uniq

  *-pred : bin → Set₀
  *-pred f = (∀ x → f x ze ≡ ze) ×
             (∀ x y → f x (S y) ≡ f x y + x)

  field
    *-uniq : isContr₂ ι *-pred

  _*_ : bin
  _*_ = proj₁ *-uniq
\end{code}      
