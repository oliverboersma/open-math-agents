import Mathlib

/-!
# A007526: a(n) = n*(a(n-1) + 1), a(0) = 0

Source: https://oeis.org/A007526
Credit: @xor2k

Formalizes the OEIS A007526 conjecture (R. J. Mathar, Dec 04 2012):
a(n) = (n+2)*a(n-1) - (2*n-1)*a(n-2) + (n-2)*a(n-3).

Conventions: offset 0 as in OEIS, with a(0) = 0 and a(n) = n*(a(n-1) + 1) for n >= 1, written
with `n + 1` in place of `n`; the terms are natural numbers. The identity is asserted for every
`n >= 3`, the smallest index at which all of a(n-1), a(n-2), a(n-3) exist; the indices
`n - 1`, `n - 2`, `n - 3` are then genuine (no truncation). Because the identity has negative
coefficients, both sides are cast to `ℤ` and evaluated there.
-/

namespace OMA.S_oeis_a007526

/-- A007526: a(0) = 0, a(n) = n*(a(n-1) + 1). -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) * (a n + 1)

/-- For every `n >= 3`, a(n) = (n+2)*a(n-1) - (2*n-1)*a(n-2) + (n-2)*a(n-3) in `ℤ`. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n →
      (a n : ℤ) = ((n : ℤ) + 2) * a (n - 1) - (2 * (n : ℤ) - 1) * a (n - 2)
        + ((n : ℤ) - 2) * a (n - 3) := by
  sorry

end OMA.S_oeis_a007526
