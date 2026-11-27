import Mathlib

/-!
# A000781: a(n) = 3 * Catalan(n) - Catalan(n - 1) - 1

Source: https://oeis.org/A000781
Credit: @AkiRA-COM-FP

Formalizes R. J. Mathar's OEIS A000781 conjectured recurrence (offset 1):
for every `n >= 5`,
`3*(n + 1)*a(n) + (-19*n + 7)*a(n - 1) + (33*n - 53)*a(n - 2) + (-21*n + 61)*a(n - 3) + 2*(2*n - 9)*a(n - 4) = 0`.
-/

namespace OMA.S_oeis_a000781

/-- Sequence `a(n) = 3 * catalan n - catalan (n - 1) - 1` (for `n >= 1`). -/
def a (n : ℕ) : ℕ :=
  3 * catalan n - catalan (n - 1) - 1

/-- For every `n >= 5`, the 4th-order linear recurrence holds. -/
theorem main :
    ∀ n : ℕ, 5 ≤ n →
      3 * ((n : ℤ) + 1) * (a n : ℤ) +
        (-19 * (n : ℤ) + 7) * (a (n - 1) : ℤ) +
        (33 * (n : ℤ) - 53) * (a (n - 2) : ℤ) +
        (-21 * (n : ℤ) + 61) * (a (n - 3) : ℤ) +
        2 * (2 * (n : ℤ) - 9) * (a (n - 4) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a000781
