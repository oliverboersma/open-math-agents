import Mathlib

/-!
# A126674: a(n) = n! * Sum_{j = 0 .. n - 1} 2^j / (j + 1)

Source: https://oeis.org/A126674
Credit: @AkiRA-COM-FP

Formalizes the OEIS A126674 conjectured recurrence (offset 0):
for every `n >= 2`, `a(n) + (-3*n + 2) * a(n - 1) + 2 * (n - 1)^2 * a(n - 2) = 0`.
-/

namespace OMA.S_oeis_a126674

/-- Sequence `a(n) = n! * Sum_{j = 0 .. n - 1} 2^j / (j + 1)` in `ℚ`. -/
def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * ∑ j ∈ Finset.range n, (2 : ℚ) ^ j / ((j : ℚ) + 1)

/-- For every `n >= 2`, `a(n) + (-3*n + 2) * a(n - 1) + 2 * (n - 1)^2 * a(n - 2) = 0`. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      a n + (-3 * (n : ℚ) + 2) * a (n - 1) +
        2 * ((n : ℚ) - 1) ^ 2 * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a126674
