\begin{code}
module T5 where
open import Relation.Binary using (DecSetoid)
open import Level using () renaming (zero to lzero)

DT : Set₁
DT = DecSetoid lzero lzero

open import T1 using (BT₁)

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

record BT₅ (t₁ : BT₁) : Set₁ where
  open BT₁ t₁ public
  open VarLangs using (XV; x)
  open DecSetoid using (Carrier)
  open DecSetoid DBool using (_≈_)
  open LogicOverL fo₁.LoL-FOL
  open fo₁ using (FOL; tt; ff)
    
  field
    induct : (e : FOL XV) →
      ⟦ e ⟧ (λ { x → Z }) →
      (∀ (y : nat) → ⟦ e ⟧ (λ {x → y}) → ⟦ e ⟧ (λ {x → S y})) →
      ∀ (y : nat) → ⟦ e ⟧ (λ {x → y})
  postulate
    decide : ∀ {W} → (Carrier W → nat) → FOL W → FOL NoVars -- T5-dec-proc
    meaning-decide : {W : DT} (env : Carrier W → nat) → (env′ : ⊥ → nat) →
      (e : FOL W) →
      let res = decide env e in
      (res ≡ tt ⊎ res ≡ ff) × (⟦ e ⟧ env) ≃ (⟦ res ⟧ env′)
\end{code}
