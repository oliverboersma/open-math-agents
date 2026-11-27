import Mathlib

/-!
# OEIS A134799: reduced denominators in a Newton iteration

Steven Finch conjectured that the reduced denominator of the iterate is three
times the corresponding term of A134799.

Source: https://oeis.org/A134799
Formalization: @senamakel
-/

namespace OMA.S_oeis_a134799

/-- Newton iteration for the reciprocal square root of 3, starting at 1/3. -/
def iterate : ℕ → ℚ
  | 0 => 1 / 3
  | n + 1 => (3 / 2) * iterate n * (1 - iterate n ^ 2)

/-- The explicit OEIS sequence. -/
def term (n : ℕ) : ℕ := 3 ^ ((3 ^ n - 1) / 2)

theorem main : ∀ n : ℕ, (iterate n).den = 3 * term n := by
  sorry

end OMA.S_oeis_a134799
