import Mathlib

/-!
# A051960: a(n) = C(n) * (3*n + 2) where C(n) are the Catalan numbers

Source: https://oeis.org/A051960
Credit: @AkiRA-COM-FP

Formalizes R. J. Mathar's OEIS A051960 conjecture (offset 0):
for every `n >= 2`, `(n + 1) * a(n) - 2 * (n + 2) * a(n - 1) - 4 * (2 * n - 3) * a(n - 2) = 0`.
-/

namespace OMA.S_oeis_a051960

/-- Sequence `a(n) = catalan(n) * (3*n + 2)`. -/
def a (n : ℕ) : ℕ :=
  catalan n * (3 * n + 2)

/-- For every `n >= 2`, `(n + 1)*a(n) - 2*(n + 2)*a(n - 1) - 4*(2*n - 3)*a(n - 2) = 0`. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      ((n : ℤ) + 1) * (a n : ℤ) - 2 * ((n : ℤ) + 2) * (a (n - 1) : ℤ) -
        4 * (2 * (n : ℤ) - 3) * (a (n - 2) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a051960
