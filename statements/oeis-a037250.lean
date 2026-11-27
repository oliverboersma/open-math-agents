import Mathlib

/-!
# A037250: a(n) = n^2 * (n^2 + 1) * (n - 1)

Source: https://oeis.org/A037250
Credit: @AkiRA-COM-FP

Formalizes the OEIS A037250 conjectured linear recurrence of signature
`(6, -15, 20, -15, 6, -1)`.
-/

namespace OMA.S_oeis_a037250

/-- Sequence `a(n) = n^2 * (n^2 + 1) * (n - 1)`. -/
def a (n : ℕ) : ℤ :=
  (n : ℤ) ^ 2 * ((n : ℤ) ^ 2 + 1) * ((n : ℤ) - 1)

/-- For every `n >= 6`, `a(n)` satisfies the linear recurrence with signature
`(6, -15, 20, -15, 6, -1)`. -/
theorem main :
    ∀ n : ℕ, 6 ≤ n →
      a n = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
        15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a037250
