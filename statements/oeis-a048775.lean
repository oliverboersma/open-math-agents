import Mathlib

/-!
# OEIS A048775: Mathar's recurrence for monotone maps from intervals

Source: https://oeis.org/A048775
Credit: @sntntHb

A048775: number of (partially defined) monotone maps from intervals of `1..n` to `1..n`
(offset 1: 1, 7, 31, 121, 456, 1709, ...). OEIS gives the closed form
`a(n) = binomial(2*n+1, n+1) - (n+1)`.

Conjecture (R. J. Mathar, Nov 30 2012):
`(n+1)*a(n) + (-7*n-2)*a(n-1) + 3*(5*n-3)*a(n-2) + (-13*n+20)*a(n-3) + 2*(2*n-5)*a(n-4) = 0`.

Formalized: `a n` is the closed form above (over `ℤ`), and `main` states the recurrence for every
`n >= 5`, the range where all of `a(n-4), ..., a(n)` lie in the sequence (offset 1).
-/

namespace OMA.S_oeis_a048775

/-- `a(n) = binomial(2*n+1, n+1) - (n+1)`. -/
def a (n : ℕ) : ℤ := ((2 * n + 1).choose (n + 1) : ℤ) - ((n : ℤ) + 1)

theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℤ) + 1) * a n + (-7 * (n : ℤ) - 2) * a (n - 1) + 3 * (5 * (n : ℤ) - 3) * a (n - 2) +
      (-13 * (n : ℤ) + 20) * a (n - 3) + 2 * (2 * (n : ℤ) - 5) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a048775
