import Mathlib

/-!
# A064757: a(n) = n * 11^n - 1

Source: https://oeis.org/A064757
Credit: @AkiRA-COM-FP

Formalizes the OEIS A064757 conjectured linear recurrence of signature
`(23, -143, 121)`.
-/

namespace OMA.S_oeis_a064757

/-- Sequence `a(n) = n * 11^n - 1`. -/
def a (n : ℕ) : ℤ :=
  (n : ℤ) * 11 ^ n - 1

/-- For every `n >= 3`, `a(n) = 23*a(n - 1) - 143*a(n - 2) + 121*a(n - 3)`. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n →
      a n = 23 * a (n - 1) - 143 * a (n - 2) + 121 * a (n - 3) := by
  sorry

end OMA.S_oeis_a064757
