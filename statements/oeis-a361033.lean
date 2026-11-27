import Mathlib

/-!
# A361033: a(n) = 3*(4*n)!/(n!*(n+1)!^3).

Source: https://oeis.org/A361033
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecture: a(n) is odd iff n = 2^k - 1 for some k >= 0.

Conventions: offset 0; the quotient is exact, computed with natural division.
-/

namespace OMA.S_oeis_a361033

/-- `a(n) = 3*(4n)!/(n!*(n+1)!^3)`. -/
def a (n : ℕ) : ℕ := 3 * (4 * n).factorial / (n.factorial * (n + 1).factorial ^ 3)

/-- `a(n)` is odd iff `n = 2^k - 1` for some `k ≥ 0`. -/
theorem main : ∀ n : ℕ, Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  sorry

end OMA.S_oeis_a361033
