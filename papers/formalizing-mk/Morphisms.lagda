\begin{code}
module Morphisms where
open import Relation.Binary using (DecSetoid)
open import Level using () renaming (zero to lzero)
open import Data.Unit renaming (tt to top)

open import T1 using (BT₁)
open import T2 using (BT₂)
open import T3 using (BT₃)
open import T4 using (BT₄)
open import T5 using (BT₅)
open import T6 using (BT₆)
open import T7 using (BT₇)
open import T8 using (BT₈)
open import Variables
open import Language using (LogicOverL)

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

7⇒8 : BT₈ →
  Σ BT₁ (λ t₁ → Σ (BT₂ t₁) (λ t₂ → Σ (BT₃ t₁ t₂) (λ t₃ → Σ (BT₄ t₁ t₂ t₃)
        (λ t₄ → Σ (BT₅ t₁) (λ t₅ → Σ (BT₆ t₂ t₅) (λ t₆ → BT₇ t₃ t₅ t₆))))))
7⇒8 record { ι = ι ; ze = ze ; S = S′ ; S≠Z = S≠Z ; inj = inj ; induct = induct ; +-uniq = +-uniq ; *-uniq = uu } =
  t₁ , (t₂ , (t₃ , (t₄ , (t₅ , (t₆ , {!!})))))
  where
    ppp = proj₁ +-uniq
    times = proj₁ uu
    t₁ : BT₁
    t₁ = record { nat = ι ; Z = ze ; S = S′ ; S≠Z = S≠Z ; inj = inj }
    t₂ : BT₂ t₁
    t₂ = record
      { _+_ = ppp
      ; right-0 = proj₁ (proj₁ (proj₂ +-uniq))
      ; x+Sy≡Sx+y = proj₂ (proj₁ (proj₂ +-uniq)) }
    t₃ : BT₃ t₁ t₂
    t₃ = record
      { _*_ = times
      ; right-zero = {!!}
      ; S* = {!!}
      ; btimes-is-* = {!!} }
    no-junk : ∀ (x : ι) → x ≡ ze ⊎ Σ ι (λ y → S′ y ≡ x)
    no-junk x = induct (λ x → x ≡ ze ⊎ Σ ι (λ y → S′ y ≡ x))
      (inj₁ refl) (λ y → {!!}) x
    t₄ : BT₄ t₁ t₂ t₃
    t₄ = record { no-junk = no-junk }
    
    t₅ : BT₅ t₁
    t₅ = record { induct = {!iii!} }
      where
        open BT₁ t₁ using (nat; Z; S; module fo₁)
        open fo₁ using (LoL-FOL; FOL)
        open VarLangs using (XV; x)
        open LogicOverL LoL-FOL using (⟦_⟧_)
        iii : (e : FOL XV) →
          ⟦_⟧_ e (λ { x → Z }) →
          ((y : nat) →
            ⟦_⟧_ e (λ { x → y }) →
            ⟦_⟧_ e (λ { x → S y })) →
          (y₁ : nat) → ⟦_⟧_ e (λ { x → y₁ })
        iii Language.FOL.tt e0 ind y = top
        iii Language.FOL.ff e0 ind y = e0
        iii (e Language.FOL.and e₁) e0 ind y =
          {!!} , {!!}
        iii (e Language.FOL.or e₁) e0 ind y = {!!}
        iii (Language.FOL.not e) e0 ind y = {!!}
        iii (e Language.FOL.⊃ e₁) e0 ind y = {!!}
        iii (y Language.FOL.== y₁) e0 ind yy = {!!}
        iii (Language.FOL.all x e) e0 ind y = {!!}
        iii (Language.FOL.exist x e) e0 ind y = {!!}
    t₆ : BT₆ t₂ t₅
    t₆ = record { induct = {!!} }
    t₇ : BT₇ t₃ t₅ t₆
    t₇ = record { induct = {!!} }
\end{code}
