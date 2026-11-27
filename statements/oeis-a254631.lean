import Mathlib

/-!
# A254631: Number of ways to write n as x*(x+1)/2 + y*(3*y+2) + z*(3*z-2) with x,y,z nonnegative integers.

Source: https://oeis.org/A254631
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A254631): `a(n) > 0` for all `n`, and `a(n) > 1` for all
`n > 35`. (Sun proved the version with `x, y, z` arbitrary integers.)

Formalization notes:
* `a n` counts ordered triples `(x, y, z)` of natural numbers; each coordinate of a solution is at
  most `n`, so counting inside `range (n + 1)` gives the full count.
* `z * (3 * z - 2)` in `ℕ` is the integer `z(3z-2)` (it is `0` for `z = 0`, and `3z ≥ 2` for
  `z ≥ 1`); `x(x+1)/2` is exact.
* With this definition `a 0, ..., a 19` = 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 2, 2, 4, 2, 2, 2
  (data of A254631), and the largest `n < 300` with `a n ≤ 1` is 35.
-/

namespace OMA.S_oeis_a254631

/-- A254631(n): the number of `(x, y, z)` with `n = x(x+1)/2 + y(3y+2) + z(3z-2)`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun t =>
    t.1 * (t.1 + 1) / 2 + t.2.1 * (3 * t.2.1 + 2) + t.2.2 * (3 * t.2.2 - 2) = n).card

/-- Sun's conjecture: `a n > 0` for all `n`, and `a n > 1` for all `n > 35`. -/
theorem main : (∀ n : ℕ, 0 < a n) ∧ ∀ n : ℕ, 35 < n → 1 < a n := by
  sorry

end OMA.S_oeis_a254631
