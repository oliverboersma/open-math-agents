import Mathlib

/-!
# A323397: a(n) = (4^n + 15*n - 1) / 9

Source: https://oeis.org/A323397
Credit: @AkiRA-COM-FP

Formalizes the OEIS A323397 conjectured linear recurrence of signature
`(6, -9, 4)`.
-/

namespace OMA.S_oeis_a323397

/-- Sequence `a(n) = (4^n + 15*n - 1) / 9` in `ℚ`. -/
def a (n : ℕ) : ℚ :=
  ((4 : ℚ) ^ n + 15 * (n : ℚ) - 1) / 9

/-- For every `n >= 3`, `a(n) = 6*a(n - 1) - 9*a(n - 2) + 4*a(n - 3)`. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n →
      a n = 6 * a (n - 1) - 9 * a (n - 2) + 4 * a (n - 3) := by
  sorry

end OMA.S_oeis_a323397
