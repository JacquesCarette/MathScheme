\AgdaHide{
\begin{code}
module NumPlus where

data ℕ+ : Set₀ where
  z+ : ℕ+
  s+ : ℕ+ → ℕ+
  _`+_ : ℕ+ → ℕ+ → ℕ+

data ℕ+X (V : Set₀) : Set₀ where
  z : ℕ+X V
  s : ℕ+X V → ℕ+X V
  _`+_ : ℕ+X V → ℕ+X V → ℕ+X V
  v : V → ℕ+X V
\end{code}
}
