import Mathlib

/-!
# On even almost perfect numbers other than powers of two

Source: https://mathoverflow.net/questions/235576/on-even-almost-perfect-numbers-other-than-powers-of-two
Credit: @mgv27

Let $\sigma(x)$ denote the sum of the divisors of $x$. If $\sigma(x) = 2x - 1$, then $x$ is
called almost perfect. If $b$ is an odd composite and
$\dfrac{b^2 - 1}{\sigma(b^2) - b^2} = \sigma(2^r)$ with $r \geq 1$, then $M = 2^r b^2$ is an
even almost perfect number. If $b = 3^k$ with $k > 1$, then
$\dfrac{b^2 - 1}{\sigma(b^2) - b^2} = 2$, and up to $10^8$ there are no other values of $b$
making this quotient prime.

(1) Is it possible to prove that if $b$ is an odd composite and
$\dfrac{b^2 - 1}{\sigma(b^2) - b^2} = q$ is prime, then necessarily $b = 3^k$ with $k > 1$?
(2) If $b$ is an odd composite and $r \geq 1$, is it possible to prove that
$\dfrac{b^2 - 1}{\sigma(b^2) - b^2} \neq \sigma(2^r)$?

Formalization notes:
* `main` states question (1) in the expected "yes" direction.
* "The quotient equals `q`" is encoded without division as `b² - 1 = q * (σ(b²) - b²)`;
  for `b > 1` we have `σ(b²) > b²`, so the natural-number subtraction is harmless.
* Odd composite: `Odd b`, `1 < b`, `¬ b.Prime`. (For prime `b = p` the quotient is `p - 1`.)
* Question (2) is a separate statement and is not formalized here.
* Pure-python check: for odd composite `b < 3000` the only prime quotients occur at
  `b = 9, 27, 81, 243, 729, 2187`, all with `q = 2`.
-/

namespace OMA.S_mo_235576

open ArithmeticFunction

/-- The quantity `σ(b²) - b²`, the sum of the proper divisors of `b²`. -/
def properSigmaSq (b : ℕ) : ℕ := ArithmeticFunction.sigma 1 (b ^ 2) - b ^ 2

/-- Question (1): if `b` is an odd composite and `(b² - 1)/(σ(b²) - b²)` is a prime `q`,
then `b = 3^k` with `k > 1`. -/
theorem main : ∀ b q : ℕ, Odd b → 1 < b → ¬ b.Prime → q.Prime →
    b ^ 2 - 1 = q * properSigmaSq b → ∃ k : ℕ, 1 < k ∧ b = 3 ^ k := by
  sorry

end OMA.S_mo_235576
