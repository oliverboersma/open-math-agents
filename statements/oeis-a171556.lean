import Mathlib

/-!
# A171556: a(n) = 3*C(n)-2, where C(n) = A000108(n).

Source: https://oeis.org/A171556
Credit: @rorcores

The entry (offset 0, data 1, 1, 4, 13, 40, 124, 394, 1285, ...) records in its FORMULA section:

  Conjecture: (n+1)*(n-2)*a(n) +(-5*n^2+11*n-4)*a(n-1) +2*(n-1)*(2*n-3)*a(n-2)=0.
  - R. J. Mathar, Sep 30 2012

Conventions:
* `C(n)` = A000108(n) is the `n`-th Catalan number, Mathlib's `catalan n` (1, 1, 2, 5, 14, ...).
  Since `catalan n ≥ 1`, the natural-number subtraction in `3 * catalan n - 2` is exact; this
  gives `a 0, ..., a 5` = 1, 1, 4, 13, 40, 124, matching the data.
* The recurrence involves `a(n-2)`, and the sequence starts at index 0, so it is stated for every
  `n ≥ 2` (the source gives no range; these are all the `n` for which the three terms exist).
* The identity is stated in `ℤ`, as written in the source (some coefficients are negative).
-/

namespace OMA.S_oeis_a171556

/-- A171556: `a n = 3 * C(n) - 2` with `C(n)` the `n`-th Catalan number. -/
def a (n : ℕ) : ℕ := 3 * catalan n - 2

/-- Mathar's conjectured recurrence:
`(n+1)(n-2) a(n) + (-5n^2+11n-4) a(n-1) + 2(n-1)(2n-3) a(n-2) = 0` for `n ≥ 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    ((n : ℤ) + 1) * ((n : ℤ) - 2) * (a n : ℤ)
      + (-5 * (n : ℤ) ^ 2 + 11 * (n : ℤ) - 4) * (a (n - 1) : ℤ)
      + 2 * ((n : ℤ) - 1) * (2 * (n : ℤ) - 3) * (a (n - 2) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a171556
