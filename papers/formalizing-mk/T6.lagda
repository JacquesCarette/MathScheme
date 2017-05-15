\AgdaHide{
\begin{code}
module T6 where
open import Relation.Binary using (DecSetoid)
open import Level using () renaming (zero to lzero)

DT : Set₁
DT = DecSetoid lzero lzero

open import T1 using (BT₁)
open import T2 using (BT₂)
open import T5 using (BT₅)

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

With the appropriate infrastructure in place, it is now possible
to define \AgdaRecord{BT₆} from the theories it extends.

\begin{code}
record BT₆ {t₁ : BT₁} (t₂ : BT₂ t₁) (t₅ : BT₅ t₁) : Set₁ where
  open VarLangs using (XV; x)
  open DecSetoid using (Carrier)
  open BT₂ t₂ public
  open fo₂ using (FOL; tt; ff; LoL-FOL; _and_; all)
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
While section~\ref{sec:cttuqe} presents the \emph{flattened} theory,
here we need only define what is new over the extended theory, namely
an induction schema, a decision procedure and its meaning formula.

Here is a guide to understanding the above definition:
\renewcommand{\labelenumi}{(\theenumi)}
\begin{enumerate*}
\item \AgdaDatatype{XV} is a (decidable) type with a single
inhabitant, \AgdaInductiveConstructor{x}.
\item All fields of \AgdaModule{BT₂} are made publicly visible for
\AgdaModule{BT₆}.
\item The language of first-order logic \AgdaDatatype{FOL} over
\AgdaBound{t₂} (and some of its constructors) is also made visible.
\item \AgdaSymbol{(λ} \AgdaSymbol{\{}\AgdaInductiveConstructor{x} \AgdaSymbol{→} \AgdaBound{y}\AgdaSymbol{\})} denotes a substitution for the single
variable \AgdaInductiveConstructor{x}.
\item \AgdaRecord{≃} denotes \emph{type equivalence}.
\end{enumerate*}
\renewcommand{\labelenumi}{\theenumi.}
