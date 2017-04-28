\begin{code}
module Variables where

open import Level using (Level; zero; suc)
open import Relation.Binary using (DecSetoid)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Bool using (Bool) renaming (_≟_ to _=𝔹_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

private
  DT : Set (suc zero)
  DT = DecSetoid zero zero

NoVars : DT
NoVars = record
  { Carrier = ⊥
  ; _≈_ = λ _ _ → ⊤
  ; isDecEquivalence = record
    { isEquivalence = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }
    ; _≟_ = λ () } }

DBool : DT
DBool = record
  { Carrier = Bool
  ; _≈_ = _≡_
  ; isDecEquivalence = record
    { isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
    ; _≟_ = _=𝔹_ } }  
    
-- For convenience, some simple "languages of variables"
module VarLangs where
  data X : Set₀ where x : X
  XV : DT
  XV = record
    { Carrier = X
    ; _≈_ = λ _ _ → ⊤
    ; isDecEquivalence = record
      { isEquivalence = record
        { refl = tt
        ; sym = λ _ → tt
        ; trans = λ _ _ → tt }
      ; _≟_ = λ _ _ → yes tt } }
\end{code}
