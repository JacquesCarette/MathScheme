
module Examples where

  module Example1 where
    open import T1
    open import Language using (module VarLangs)
    open import NatVar using (ℕS; s; v)
    open VarLangs -- a single variable
    
  -- an example: ∀ x. not (S x == S (S x))
    open fo₁
    ex : FOL XV 
    ex = all x (P (s (v x) == s (s (v x))))
