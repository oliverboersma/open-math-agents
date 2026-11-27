import Mathlib

/-!
# A066049: Numbers k such that 2*k^2 - 1 is a prime.

Source: https://oeis.org/A066049
Credit: @LAPRAI

Formalizes the OEIS comment: It is conjectured that this sequence is infinite.

Conventions: natural numbers `k`; for `k ≥ 1` the subtraction is exact.
-/

namespace OMA.S_oeis_a066049

/-- There are infinitely many `k` with `2k^2 - 1` prime. -/
theorem main : {k : ℕ | (2 * k ^ 2 - 1).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a066049
