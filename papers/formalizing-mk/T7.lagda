\AgdaHide{
\begin{code}
module T7 where
open import Relation.Binary using (DecSetoid)
open import Level using () renaming (zero to lzero)

DT : Set₁
DT = DecSetoid lzero lzero

open import T1 using (BT₁)
open import T2 using (BT₂)
open import T3 using (BT₃)
open import T5 using (BT₅)
open import T6 using (BT₆)

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ;_×_;_,_)
open import Data.Bool using (Bool)
open import Equiv using (_≃_)

open import Variables using (module VarLangs; NoVars; DBool)
open import Language
  using (module FOL;
         module LogicOverL)
\end{code}
}

\begin{code}
record BT₇ {t₁ : BT₁} {t₂ : BT₂ t₁} (t₃ : BT₃ t₁ t₂) (t₅ : BT₅ t₁) (t₆ : BT₆ t₂ t₅) : Set₁ where
  open VarLangs using (XV; x)
  open DecSetoid using (Carrier)
  open BT₃ t₃ public
  open fo₃ using (FOL; tt; ff; LoL-FOL; _and_; all)
  open LogicOverL LoL-FOL

  field
    induct : (e : FOL XV) →
      ⟦ e ⟧ (λ { x → ⟦ 0 ⟧₁ }) →
      (∀ y → ⟦ e ⟧ (λ {x → y}) → ⟦ e ⟧ (λ {x → S y})) →
      ∀ y → ⟦ e ⟧ (λ {x → y})
  postulate
    decide : ∀ {W} → (Carrier W → nat) → FOL W → FOL NoVars
    meaning-decide : {W : DT} (env : Carrier W → nat) → (env′ : ⊥ → nat) →
      (e : FOL W) →
      let res = decide env e in
      (res ≡ tt ⊎ res ≡ ff) × (⟦ e ⟧ env) ≃ (⟦ res ⟧ env′)
\end{code}


