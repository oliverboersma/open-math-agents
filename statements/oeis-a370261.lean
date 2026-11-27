import Mathlib

/-!
# A370261: a(n) = sqrt(A370259(2*n)/(n+1)) for n >= 1.

Source: https://oeis.org/A370261
Credit: @marcelopierry

Conjecture (in the comments of A370261): the sequence is integral.

Conventions:
* A370259(n) = (T(n, n+1) - 1)/n^3 for n >= 1, where T(n, x) is the n-th Chebyshev polynomial
  of the first kind (Mathlib's `Polynomial.Chebyshev.T` over the integers, evaluated at n + 1).
  The quotient is taken in the rationals (data 1, 2, 9, 75, 961, 16900, ...).
* a(n) = sqrt(A370259(2n)/(n+1)) is the real square root (offset 1; data 1, 5, 65, 1449, ...).
* Integral is stated as: for every n >= 1, a(n) is a natural number (a square root is
  nonnegative, so this is the same as being an integer).
-/

namespace OMA.S_oeis_a370261

open Polynomial

/-- A370259(n) = (T(n, n+1) - 1)/n^3. -/
noncomputable def A370259 (n : ℕ) : ℚ :=
  ((((Chebyshev.T ℤ (n : ℤ)).eval ((n : ℤ) + 1) : ℤ) : ℚ) - 1) / (n : ℚ) ^ 3

/-- A370261(n) = sqrt(A370259(2n)/(n+1)). -/
noncomputable def a (n : ℕ) : ℝ := Real.sqrt ((A370259 (2 * n) : ℝ) / ((n : ℝ) + 1))

/-- The conjecture: A370261 is integral. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, a n = k := by
  sorry

end OMA.S_oeis_a370261
