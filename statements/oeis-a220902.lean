import Mathlib

/-!
# A220902: Catalan(n) - A000245(n-2)

Source: https://oeis.org/A220902
Credit: @sntntHb

The sequence (offset 2: `a(2) = 2, a(3) = 4, a(4) = 11, a(5) = 33, ...`) is
`a(n) = Catalan(n) - A000245(n-2)`, equivalently (Andrei Asinowski, Dec 16 2015)
`a(n) = Catalan(n) - Catalan(n-1) + Catalan(n-2)`; we use the latter closed form as the definition.
The entry records the conjecture (R. J. Mathar, May 30 2014):
`Conjecture: (n+1)*a(n) + (-5*n+3)*a(n-1) + (5*n-13)*a(n-2) + 2*(-2*n+9)*a(n-3) = 0.`

Since the offset is 2 and the recurrence involves `a(n-3)`, it is stated for `n ≥ 5`, the range where
all terms are defined. The identity is stated over `ℤ`. Mathlib's `catalan` is A000108.
-/

namespace OMA.S_oeis_a220902

/-- `a n = Catalan(n) - Catalan(n-1) + Catalan(n-2)` (OEIS A220902, for `n ≥ 2`). -/
def a (n : ℕ) : ℤ := (catalan n : ℤ) - (catalan (n - 1) : ℤ) + (catalan (n - 2) : ℤ)

/-- R. J. Mathar's conjectured recurrence for OEIS A220902. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℤ) + 1) * a n + (-5 * (n : ℤ) + 3) * a (n - 1) + (5 * (n : ℤ) - 13) * a (n - 2) +
      2 * (-2 * (n : ℤ) + 9) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a220902
