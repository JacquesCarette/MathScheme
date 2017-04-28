\AgdaHide{
\begin{code}
module T2a where
open import T1 using (BT₁)
open import T2 using (BT₂)
open import Numerals

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; sym; cong₂)
open import Data.Nat using (ℕ; suc) -- instead of defining our own
  -- isomorphic copy
open import Data.Vec using (_∷_; []; Vec)

-------------------------------------------------------------------
-- an extension of BT₂ that assumes commutativity and associativity
record BT₂ext {t1 : BT₁} (t2 : BT₂ t1) : Set₀ where
  open BT₂ t2 public
  field
    -- commutativity is needed for some proofs
    -- and is not provable; neither is associativity,
    -- in general.  So while this is more than Q,
    -- it is still 'ok' in the sense that these are
    -- equational axioms and not schemas.
    comm-+ : ∀ x y → x + y ≡ y + x
    assoc-+ : ∀ x y z → (x + y) + z ≡ x + (y + z)

  -- useful below. 
  left-0 : ∀ x → Z + x ≡ x
  left-0 x = trans (comm-+ Z x) (right-0 x)

  -- to show that this definition is correct, we need a number
  -- of properties
  shift-S : ∀ x y → x + S y ≡ S x + y
  shift-S x y = trans (x+Sy≡Sx+y x y) (
                trans (cong S (comm-+ x y)) (
                trans (sym (x+Sy≡Sx+y y x)) (
                      (comm-+ y (S x)))) )

  -- two different ways of writing 2x+2
  2x+2 : ∀ x → S x + S x ≡ S ((x + x) + S Z)
  2x+2 x = trans (x+Sy≡Sx+y (S x) x)
                 (cong S (trans (comm-+ (S x) x) (
                          trans (x+Sy≡Sx+y x x) (
                          trans (cong S (sym (right-0 (x + x)))) (
                                (sym (x+Sy≡Sx+y (x + x) Z)))))))

  shuffle : ∀ x y → (x + y) + (x + y) ≡ (x + x) + (y + y)
  shuffle x y = trans (assoc-+ x y (x + y))
                (trans (cong (λ z → x + z) (trans (sym (assoc-+ y x y))
                                           (trans (cong (λ z → z + y) (comm-+ y x))
                                                  (assoc-+ x y y))))
                (sym (assoc-+ x x _)))

  add1-is-S : ∀ x → ⟦ 1b ⟧₂ + x ≡ S x
  add1-is-S x = trans (cong (λ z → z + x) (lemma₂)) (
                trans (comm-+ (S Z) x) (
                trans (x+Sy≡Sx+y x Z)
                      (cong S (right-0 x))))

  +1-is-S : ∀ x → ⟦ +1 x ⟧₂ ≡ S ⟦ x ⟧₂
  +1-is-S (bn (zero ∷ l)) = x+Sy≡Sx+y (unroll l + unroll l) Z
  +1-is-S (bn (one ∷ [])) =
    trans (right-0 _) (
    trans (cong (λ x → ⟦ 1b ⟧₂ + x) lemma₂) (
    trans (x+Sy≡Sx+y _ Z)
          (cong S (right-0 _))))
  +1-is-S (bn (one ∷ x ∷ x₁)) =
    trans (<<-is-*2 (+1 (bn (x ∷ x₁)))) (
    trans (cong₂ _+_ (+1-is-S (bn (x ∷ x₁))) (+1-is-S (bn (x ∷ x₁))))
          (2x+2 _))

  -- because of the invariants that we keep in the types, and the
  -- way that bplus is defined _as a function_, we can actually
  -- prove the meaning function 'internally'.  Only needs 8 cases
  -- whereas the paper proof needs 10 (?).
  -- Plus I have no idea if the paper spec is complete.
\end{code}
}
\begin{code}
  bplus-is-+ : ∀ x y → ⟦ bplus x y ⟧₂ ≡ ⟦ x ⟧₂ + ⟦ y ⟧₂
\end{code}
\AgdaHide{
\begin{code}
  bplus-is-+ (bn {0} (zero ∷ [])) y = trans (sym (left-0 ⟦ y ⟧₂)) (cong (λ z → z + ⟦ y ⟧₂) (sym lemma₁))
  bplus-is-+ (bn {0} (one ∷ [])) y = trans (+1-is-S y) (sym (add1-is-S ⟦ y ⟧₂))
  bplus-is-+ (bn {suc n} (d₀ ∷ l₀)) (bn {ℕ.zero} (zero ∷ [])) =
    trans (sym (right-0 _)) (cong (λ x → ⟦ bn (d₀ ∷ l₀) ⟧₂ + x) (sym lemma₁))
  bplus-is-+ (bn {suc n} (d₀ ∷ l₀)) (bn {ℕ.zero} (one ∷ [])) = 
    let num = bn (d₀ ∷ l₀) in
    trans (+1-is-S num) (x+1 ⟦ num ⟧₂) 
  bplus-is-+ (bn {suc n} (zero ∷ l₀)) (bn {suc n₁} (zero ∷ l₁)) = 
    let n₁ = bn l₀
        n₂ = bn l₁
        num = bplus n₁ n₂
        v₁ = ⟦ n₁ ⟧₂
        v₂ = ⟦ n₂ ⟧₂ in
    trans (<<-is-*2 num) (trans (cong₂ _+_ (bplus-is-+ n₁ n₂) (bplus-is-+ n₁ n₂))
    (trans (cong (λ z → z + (v₁ + v₂)) (comm-+ v₁ v₂))
    (trans (assoc-+ v₂ v₁ _) (
     trans (cong (λ z → v₂ + z) (trans (sym (assoc-+ v₁ v₁ v₂)) (cong (λ z → z + v₂) (sym (<<-is-*2 n₁)))))
    (trans (comm-+ v₂ _) (
    trans (assoc-+ _ v₂ v₂)
          (cong (λ z → ⟦ << n₁ ⟧₂ + z) (sym (<<-is-*2 n₂)))))))))
  bplus-is-+ (bn {suc n} (zero ∷ l₀)) (bn {suc n₁} (one ∷ l₁)) =
    let n₁ = bn l₀
        n₂ = bn l₁
        num = bplus n₁ n₂
        v₁ = ⟦ n₁ ⟧₂
        v₂ = ⟦ n₂ ⟧₂ in
    trans (+1-is-S (<< num)) (
    trans (cong S (trans (<<-is-*2 num)
                  (trans (cong₂ _+_ (bplus-is-+ n₁ n₂) (bplus-is-+ n₁ n₂))
                         (shuffle v₁ v₂))))
    (trans (sym (x+Sy≡Sx+y (v₁ + v₁) (v₂ + v₂)))
          (cong₂ _+_ (sym (<<-is-*2 n₁))
                     (trans (x+1 _)
                            (cong₂ _+_ (trans (sym (<<-is-*2 n₂)) (right-0 _)) lemma₂)))))
  bplus-is-+ (bn {suc n} (one ∷ l₀)) (bn {suc n₁} (zero ∷ l₁)) =
    let n₁ = bn l₀
        n₂ = bn l₁
        num = bplus n₁ n₂
        v₁ = ⟦ n₁ ⟧₂
        v₂ = ⟦ n₂ ⟧₂ in
     trans (+1-is-S (<< num)) (
     trans (cong S (trans (<<-is-*2 num)
                   (trans (cong₂ _+_ (bplus-is-+ n₁ n₂) (bplus-is-+ n₁ n₂))
                   (trans (shuffle v₁ v₂)
                          (comm-+ _ _)))))
     (trans (sym (x+Sy≡Sx+y _ _))
     (trans (comm-+ _ _) (cong₂ _+_ (trans (x+1 _) (trans (cong₂ _+_ (sym (<<-is-*2 n₁)) lemma₂) (cong (λ z → z + S Z) (right-0 _))))
                                    (sym (<<-is-*2 n₂))))))
  bplus-is-+ (bn {suc n} (one ∷ l₀)) (bn {suc n₁} (one ∷ l₁)) =
    let n₁ = bn l₀
        n₂ = bn l₁
        num = bplus n₁ n₂
        v₁ = ⟦ n₁ ⟧₂
        v₂ = ⟦ n₂ ⟧₂ in
     trans (+1-is-S (+1 (<< num)))
     (trans (cong S (+1-is-S (<< num)))
     (trans (cong (λ z → S (S z)) (trans (<<-is-*2 num)
                                  (trans (cong₂ _+_ (bplus-is-+ n₁ n₂) (bplus-is-+ n₁ n₂))
                                  (shuffle v₁ v₂))))
     (trans (cong S (trans (sym (x+Sy≡Sx+y _ _)) (comm-+ _ _)))
     (trans (sym (x+Sy≡Sx+y _ _))
     (trans (comm-+ _ _)
            (cong₂ _+_ (trans (cong S (sym (<<-is-*2 n₁))) (sym (x+Sy≡Sx+y _ _)))
                       (trans (cong S (sym (<<-is-*2 n₂))) (sym (x+Sy≡Sx+y _ _)))))))))
\end{code}
}
