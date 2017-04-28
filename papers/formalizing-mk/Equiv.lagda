\begin{code}
{-# OPTIONS --without-K #-}

module Equiv where

open import Level using (_⊔_)
open import Function using (_∘_; id; flip)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

infix 4 _∼_
infix 4 _≃_
infixr 5 _●_

------------------------------------------------------------------------------
-- Extensional equivalence of (unary) functions

_∼_ : ∀ {ℓ ℓ'} → {A : Set ℓ} {B : Set ℓ'} → (f g : A → B) → Set (ℓ ⊔ ℓ')
_∼_ {A = A} f g = (x : A) → f x ≡ g x

refl∼ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} → (f ∼ f)
refl∼ _ = refl

sym∼ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g : A → B} → (f ∼ g) → (g ∼ f)
sym∼ H x = sym (H x)

trans∼ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g h : A → B} → (f ∼ g) → (g ∼ h) → (f ∼ h)
trans∼ H G x = trans (H x)  (G x)

∘-resp-∼ : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} {f h : B → C} {g i : A → B} →
  (f ∼ h) → (g ∼ i) → f ∘ g ∼ h ∘ i
∘-resp-∼ {f = f} {i = i} f∼h g∼i x = trans (cong f (g∼i x)) (f∼h (i x))

isEquivalence∼ : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → IsEquivalence (_∼_ {ℓ} {ℓ′} {A} {B})
isEquivalence∼ = record { refl = refl∼ ; sym = sym∼ ; trans = trans∼ }

------------------------------------------------------------------------------
-- Quasi-equivalences, in a more useful packaging

record _≃_ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor qeq
  field
    f : A → B
    g : B → A
    α : (f ∘ g) ∼ id
    β : (g ∘ f) ∼ id
    -- to make it contractible, could add
    -- τ : ∀ x → cong f (β x) P.≡ α (f x)

id≃ : ∀ {ℓ} {A : Set ℓ} → A ≃ A
id≃ = qeq id id (λ _ → refl) (λ _ → refl)

sym≃ : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → (A ≃ B) → B ≃ A
sym≃ (qeq f g α β) = qeq g f β α

trans≃ :  ∀ {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} →
  A ≃ B → B ≃ C → A ≃ C
trans≃ {A = A} {B} {C} (qeq f f⁻¹ fα fβ) (qeq g g⁻¹ gα gβ) =
  qeq (g ∘ f) (f⁻¹ ∘ g⁻¹) (λ x → trans (cong g (fα (g⁻¹ x))) (gα x))
                          (λ x → trans (cong f⁻¹ (gβ (f x))) (fβ x))

-- more convenient infix version, flipped

_●_ : ∀ {ℓ ℓ′ ℓ″} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} →
  B ≃ C → A ≃ B → A ≃ C
_●_ = flip trans≃

≃IsEquiv : IsEquivalence {Level.suc Level.zero} {Level.zero} {Set} _≃_
≃IsEquiv = record { refl = id≃ ; sym = sym≃ ; trans = trans≃ }

-- equivalences are injective

inj≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} →
  (eq : A ≃ B) → (x y : A) → (_≃_.f eq x ≡ _≃_.f eq y → x ≡ y)
inj≃ (qeq f g α β) x y p = trans
  (sym (β x)) (trans
  (cong g p) (
  β y))
\end{code}
