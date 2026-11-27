import Mathlib

/-!
# A097814: Expansion of e.g.f. exp(3*x) / (1 - 3*x)

Source: https://oeis.org/A097814
Credit: @AkiRA-COM-FP

Formalizes R. J. Mathar's OEIS A097814 conjectured recurrence (offset 0):
for every `n >= 2`, `a(n) + 3*(-n - 1)*a(n - 1) + 9*(n - 1)*a(n - 2) = 0`,
where `a(0) = 1` and `a(n) = 3*n*a(n - 1) + 3^n` for `n > 0`.
-/

namespace OMA.S_oeis_a097814

/-- Sequence defined by `a(0) = 1` and `a(n + 1) = 3*(n + 1)*a(n) + 3^(n + 1)`. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => 3 * (n + 1) * a n + 3 ^ (n + 1)

/-- For every `n >= 2`, `a(n) + 3*(-n - 1)*a(n - 1) + 9*(n - 1)*a(n - 2) = 0`. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      (a n : ℤ) + 3 * (-(n : ℤ) - 1) * (a (n - 1) : ℤ) +
        9 * ((n : ℤ) - 1) * (a (n - 2) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a097814
