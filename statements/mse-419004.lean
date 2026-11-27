import Mathlib

/-!
# Are there infinitely many semi primes of the form $x^2 + 2x$ for integral $x$?

Source: https://math.stackexchange.com/questions/419004/are-there-infinitely-many-semi-primes-of-the-form-x2-2x-for-integral-x
Credit: @mgv27

Are there infinitely many semiprimes of the form $x^2 + 2x$ for integral $x$?

Formalization notes:
* A semiprime is a natural number with exactly two prime factors counted with
  multiplicity, i.e. `n.primeFactorsList.length = 2` (this is `Ω(n) = 2`).
* `x` ranges over `ℤ`; only values with `x^2 + 2x > 0` can be semiprimes, and we require
  this explicitly before passing to `ℕ` with `Int.toNat`.
* Since `x^2 + 2x = x(x+2)`, for `x > 2` this is semiprime iff `x, x+2` are twin primes,
  so the question is equivalent to the twin prime conjecture (as the answer notes).
  `main` states the expected "yes" direction.
-/

namespace OMA.S_mse_419004

/-- `n` is a semiprime: it has exactly two prime factors counted with multiplicity. -/
def IsSemiprime (n : ℕ) : Prop :=
  n.primeFactorsList.length = 2

/-- There are infinitely many integers `x` with `x^2 + 2x` a (positive) semiprime. -/
theorem main :
    Set.Infinite {x : ℤ | 0 < x ^ 2 + 2 * x ∧ IsSemiprime (x ^ 2 + 2 * x).toNat} := by
  sorry

end OMA.S_mse_419004
