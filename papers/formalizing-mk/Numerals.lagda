\AgdaHide{
\begin{code}
module Numerals where
\end{code}
\noindent Rather that defining our own isomorphic copy, re-use
ℕ and Vec.

\begin{code}
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (_∷_; []; Vec)
\end{code}

plus is a \emph{function} on ℕ, which will (of course)
implement addition.  Note that this is not a 'good'
function, in the sense that it is extremely inefficient.
it does have the advantage of being simple and facilitate
proofs.  Note that it is defined (on purpose) by recursion
on the left argument, while the properties in T2
turn out to be "recursive" on the right.

\begin{code}
plus : ℕ → ℕ → ℕ
plus 0 y = y
plus (suc x) y = suc (plus x y)
\end{code}
}

We represent numerals as vectors (of length at least $1$) of
binary digits.

\begin{code}
data BinDigit : Set where zero one : BinDigit
data BNum : Set where
  bn : {n : ℕ} → Vec BinDigit (suc n) → BNum
\end{code}

\noindent This then allows a straightforward implementation of
\AgdaFunction{bplus} to add numerals.  It is then
possible to \emph{prove} that the meaning function for
\AgdaFunction{bplus} is a theorem.

\AgdaHide{
\noindent Convenient abbreviations

\begin{code}
0b 1b 2b : BNum
0b = bn (zero ∷ [])
1b = bn (one ∷ [])
2b = bn (zero ∷ one ∷ [])

<< : BNum → BNum
<< (bn l) = bn (zero ∷ l)
\end{code}

\noindent Note how +1 is defined by induction on BNum.

\begin{code}
+1 : BNum → BNum
+1 (bn (zero ∷ l)) = bn (one ∷ l)
+1 (bn (one ∷ [])) = bn (zero ∷ one ∷ [])
+1 (bn (one ∷ x ∷ l)) = << (+1 (bn (x ∷ l)))
\end{code}

Now we want to define a transformer on BNum
with a "meaning formula" that says that it is addition.
this too is defined by induction on BNum
bplus is essentially ξ₃.  It is not the only
such transformer, as different representations could
be even more efficient.
It is also kind of ξ₄ !  What happens it that all the
conditions are all vacuously true.  So the axioms are
then just a bunch of pattern-match.  Turns out that
the rules below are more 'syntax directed' than the
ones given in the axioms.

\begin{code}
bplus : BNum → BNum → BNum
bplus (bn {0} (zero ∷ [])) y = y
bplus (bn {0} (one ∷ [])) y = +1 y
bplus (bn {suc n} (d₀ ∷ l₀)) (bn {ℕ.zero} (zero ∷ [])) = bn (d₀ ∷ l₀)
bplus (bn {suc n} (d₀ ∷ l₀)) (bn {ℕ.zero} (one ∷ [])) = +1 (bn (d₀ ∷ l₀))
bplus (bn {suc n} (zero ∷ l₀)) (bn {suc m} (zero ∷ l₁)) = 
          << (bplus (bn l₀) (bn l₁))
bplus (bn {suc n} (one ∷ l₀)) (bn {suc m} (zero ∷ l₁)) =
      +1 (<< (bplus (bn l₀) (bn l₁)))
bplus (bn {suc n} (zero ∷ l₀)) (bn {suc m} (one ∷ l₁)) =
      +1 (<< (bplus (bn l₀) (bn l₁)))
bplus (bn {suc n} (one ∷ l₀)) (bn {suc m} (one ∷ l₁)) = 
  +1 (+1 (<< (bplus (bn l₀) (bn l₁))))
\end{code}

Important: because BNum is a type, there is no need for
is-bnum, as it is simply true by construction.  However,
here BNum is an explicit representation (as a Vector of digits)
whereas in {\churchuqe} it is done as a 'recognizer of expressions'
which picksout expressions which are made up of sequences of
digits.  The sequencing is buried (as a right-leaning tree) in
a bunch of 'bnat' calls.  If we're going to go through codes
to represent things, may as well use codes which are specially
built for the task!

Of course, we will need an interpretation of BNum in nat,
but that will be done inside T2.

For btimes, rather than be axiomatic, we go directly to a transformer.

\begin{code}
_btimes_ : BNum → BNum → BNum
x btimes bn (zero ∷ []) = 0b
x btimes bn (one ∷ []) = x
bn (zero ∷ []) btimes bn (x₂ ∷ x₃ ∷ x₄) = 0b
bn (one ∷ []) btimes bn (x₂ ∷ x₃ ∷ x₄) = bn (x₂ ∷ x₃ ∷ x₄)
bn (zero ∷ x₁ ∷ x₂) btimes bn (x₃ ∷ x₄ ∷ x₅) =
         << (bn (x₁ ∷ x₂) btimes bn (x₃ ∷ x₄ ∷ x₅))
bn (one ∷ x₁ ∷ x₂) btimes bn (x₃ ∷ x₄ ∷ x₅) =
  let y = bn (x₃ ∷ x₄ ∷ x₅) in
  bplus (<< (bn (x₁ ∷ x₂) btimes y)) y
\end{code}
}
