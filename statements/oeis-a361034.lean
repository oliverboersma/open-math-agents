import Mathlib

/-!
# A361034: a(n) = 2520*(4*n)!/(n!*(n+2)!^3).

Source: https://oeis.org/A361034
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecture: a(n) is odd iff n = 2^k - 2 for some k >= 1.

Conventions: offset 0; the quotient is exact, computed with natural division.
-/

namespace OMA.S_oeis_a361034

/-- `a(n) = 2520*(4n)!/(n!*(n+2)!^3)`. -/
def a (n : ℕ) : ℕ := 2520 * (4 * n).factorial / (n.factorial * (n + 2).factorial ^ 3)

/-- `a(n)` is odd iff `n = 2^k - 2` for some `k ≥ 1`. -/
theorem main : ∀ n : ℕ, Odd (a n) ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k - 2 := by
  sorry

end OMA.S_oeis_a361034
