\begin{code}
module T4 where
open import T1 using (BT₁)
open import T2 using (BT₂)
open import T3 using (BT₃)
open import Numerals

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ)

record BT₄ (t1 : BT₁) (t2 : BT₂ t1) (t3 : BT₃ t1 t2) : Set₀ where
  open BT₃ t3 public
  field
    no-junk : ∀ x → x ≡ Z ⊎ Σ nat (λ y → S y ≡ x)
\end{code}
