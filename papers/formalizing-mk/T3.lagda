\begin{code}
module T3 where
open import T1 using (BT₁)
open import T2 using (BT₂)
open import Numerals using (_btimes_)
open import NumPlusTimes
open import Language using (GroundLanguage; module FOL)

open import Level renaming (zero to lzero)
open import Relation.Binary using (DecSetoid)
open DecSetoid using (Carrier)
open import Relation.Binary.PropositionalEquality using (_≡_)
private
  DT = DecSetoid lzero lzero

record BT₃ (t₁ : BT₁) (t₂ : BT₂ t₁) : Set₀ where
  open BT₂ t₂ public

  field
    _*_ : nat → nat → nat
    right-zero : ∀ x → x * Z ≡ Z
    S* : ∀ x y → x * S y ≡ (x * y) + x
    btimes-is-* : ∀ a b → ⟦ a btimes b ⟧₂ ≡ ⟦ a ⟧₂ * ⟦ b ⟧₂

  nat*-lang : GroundLanguage nat
  nat*-lang = record { Lang = λ X → ℕ* (Carrier X)
                     ; value = λ {V} → val {V} }
   where
    val : {V : DT} → ℕ* (Carrier V) → (Carrier V → nat) → nat
    val     z        env = Z
    val {V} (s n)    env = S (val {V} n env)
    val {V} (e `+ f) env = val {V} e env + val {V} f env
    val {V} (e `* f) env = val {V} e env + val {V} f env
    val     (v x)    env = env x

  module fo₃ = FOL nat*-lang
\end{code}
