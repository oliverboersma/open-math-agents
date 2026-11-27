import Mathlib

/-!
# A010845: a(n) = 3 * n * a(n - 1) + 1 with a(0) = 1

Source: https://oeis.org/A010845
Credit: @AkiRA-COM-FP

Formalizes the OEIS A010845 conjectured recurrence (offset 0):
for every `n >= 2`, `a(n) + (-3*n - 1) * a(n - 1) + 3 * (n - 1) * a(n - 2) = 0`.
-/

namespace OMA.S_oeis_a010845

/-- Sequence defined by `a(0) = 1` and `a(n + 1) = 3 * (n + 1) * a(n) + 1`. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => 3 * (n + 1) * a n + 1

/-- For every `n >= 2`, `a(n) + (-3*n - 1)*a(n - 1) + 3*(n - 1)*a(n - 2) = 0`. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      (a n : ℤ) + (-3 * (n : ℤ) - 1) * (a (n - 1) : ℤ) +
        3 * ((n : ℤ) - 1) * (a (n - 2) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a010845
