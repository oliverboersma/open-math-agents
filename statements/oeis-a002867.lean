import Mathlib

/-!
# A002867: a(n) = binomial(n,floor(n/2))*(n+1)!.

Source: https://oeis.org/A002867
Credit: @rorcores

The entry (offset 0, data 1, 2, 12, 72, 720, 7200, 100800, ...) records in its FORMULA section:

  Conjecture: a(n) - 2*a(n-1) - 4*n*(n-1)*a(n-2) = 0. - R. J. Mathar, Nov 24 2012

Conventions:
* `a n = binomial(n, floor(n/2)) * (n+1)!` for `n ≥ 0`, exactly the name of the sequence;
  `floor(n/2)` is the natural-number quotient `n / 2`. This gives `a 0, ..., a 5` = 1, 2, 12, 72,
  720, 7200, matching the data.
* The recurrence involves `a(n-2)`, and the sequence starts at index 0, so it is stated for every
  `n ≥ 2` (the source gives no range; these are all the `n` for which the three terms exist).
* The identity is stated in `ℤ`, as written in the source, so that no truncated subtraction occurs.
-/

namespace OMA.S_oeis_a002867

/-- A002867: `a n = binomial(n, floor(n/2)) * (n+1)!`. -/
def a (n : ℕ) : ℕ := n.choose (n / 2) * (n + 1).factorial

/-- Mathar's conjectured recurrence: `a(n) - 2 a(n-1) - 4 n (n-1) a(n-2) = 0` for `n ≥ 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (a n : ℤ) - 2 * (a (n - 1) : ℤ) - 4 * (n : ℤ) * ((n : ℤ) - 1) * (a (n - 2) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a002867
