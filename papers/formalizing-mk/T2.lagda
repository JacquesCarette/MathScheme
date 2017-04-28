\AgdaHide{
\begin{code}
module T2 where
open import T1 using (BT₁)
open import Numerals
open import NumPlus
open import NatVar using (ℕX)

open import Relation.Binary using (DecSetoid)
open DecSetoid using (Carrier)
open import Level using () renaming (zero to lzero)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; sym; cong₂)
open import Data.Nat using (ℕ; suc) -- instead of defining our own
  -- isomorphic copy
open import Data.Vec using (_∷_; []; Vec)
open import Language using (GroundLanguage; module FOL)
open GroundLanguage using (value)

private
  DT = DecSetoid lzero lzero
-------------------------------------------------------------------
    
record BT₂ (t1 : BT₁) : Set where
  open BT₁ t1 public
  field
    _+_ : nat → nat → nat
    right-0 : ∀ x → x + Z ≡ x
    x+Sy≡Sx+y : ∀ x y → x + S y ≡ S (x + y)
    -- Wikipedia lists
    -- y ≡ 0 ⊎ Σ ℕ (λ x → S x ≡ y)
    -- as an additional axiom.  It allows addition
    -- to be defined recursively.

  bnat : nat → nat → nat
  bnat x y = (x + x) + y

  -- the following two functions are not (unfortunately)
  -- private, as T2a will need to prove things about them.
  dig-to-nat : BinDigit → nat
  dig-to-nat zero = Z
  dig-to-nat one = S Z

  unroll : {n : ℕ} → Vec BinDigit n → nat
  unroll [] = Z
  unroll (x ∷ l) = bnat (unroll l) (dig-to-nat x)

  ⟦_⟧₂ : BNum → nat
  ⟦ bn (x ∷ l) ⟧₂ = bnat (unroll l) (dig-to-nat x)

  -- just to make sure we've done things right.
  lemma₁ : ⟦ 0b ⟧₂ ≡ Z
  lemma₁ = trans (right-0 _) (right-0 Z)

  lemma₂ : ⟦ 1b ⟧₂ ≡ S Z
  lemma₂ = trans (cong (λ z → z + S Z) (right-0 Z)) (
           trans (x+Sy≡Sx+y Z Z)
                 (cong S (right-0 Z)))

  -- two coherence theorems are provable here (<< x is x + x and + 1 on the right is S)
  <<-is-*2 : ∀ x → ⟦ << x ⟧₂ ≡ ⟦ x ⟧₂ + ⟦ x ⟧₂
  <<-is-*2 (bn (x ∷ x₁)) = let num = ⟦ bn (x ∷ x₁) ⟧₂ in right-0 (num + num)

  x+1 : ∀ x → S x ≡ x + ⟦ 1b ⟧₂
  x+1 x = sym (trans (cong (λ z → x + z) lemma₂) (
               trans (x+Sy≡Sx+y x Z) (
               cong S (right-0 x))))

  nat+-lang : GroundLanguage nat
  nat+-lang = record { Lang = λ X → ℕ+X (Carrier X)
                     ; value = λ {V} → val {V} }
   where
    val : {V : DT} → ℕ+X (Carrier V) → (Carrier V → nat) → nat
    val     z        env = Z
    val {V} (s n)    env = S (val {V} n env)
    val {V} (e `+ f) env = val {V} e env + val {V} f env
    val     (v x)    env = env x

  module fo₂ = FOL nat+-lang

  -- we can inject ℕX into ℕ+X
  inject1⇒2 : ∀{V} → ℕX V → ℕ+X V
  inject1⇒2 ℕX.z     = z
  inject1⇒2 (ℕX.s t) = s (inject1⇒2 t)
  inject1⇒2 (ℕX.v x) = v x
\end{code}
}
