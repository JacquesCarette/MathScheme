\begin{code}
module NumPlusTimes where

data ℕ* (V : Set₀) : Set₀ where
  z : ℕ* V
  s : ℕ* V → ℕ* V
  _`+_ : ℕ* V → ℕ* V → ℕ* V
  _`*_ : ℕ* V → ℕ* V → ℕ* V
  v : V → ℕ* V
\end{code}
