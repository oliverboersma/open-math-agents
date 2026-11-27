import Mathlib

/-!
# A254668: Number of ways to write n as the sum of a square, a second pentagonal number, and a hexagonal number.

Source: https://oeis.org/A254668
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A254668): `a(n) > 0` for all `n`. Also, `a(n) = 1` only for
`n = 0, 5, 13, 14, 20, 112, 125`.

Formalization notes:
* The square is `x^2`, the second pentagonal number `y(3y+1)/2` and the hexagonal number
  `z(2z-1)`, with `x, y, z` nonnegative integers (as in the examples of A254668, e.g.
  `20 = 2^2 + 3(3*3+1)/2 + 1(2*1-1)`).
* `a n` counts ordered triples `(x, y, z)`; each coordinate of a solution is at most `n`, so
  counting inside `range (n + 1)` gives the full count.
* With this definition `a 0, ..., a 24` = 1, 2, 2, 2, 2, 1, 2, 3, 3, 3, 2, 2, 3, 1, 1, 3, 5, 6, 2,
  3, 1, 2, 4, 2, 4 (data of A254668), and the `n < 200` with `a n = 1` are 0, 5, 13, 14, 20, 112,
  125.
-/

namespace OMA.S_oeis_a254668

/-- A254668(n): the number of `(x, y, z)` with `n = x^2 + y(3y+1)/2 + z(2z-1)`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun t =>
    t.1 ^ 2 + t.2.1 * (3 * t.2.1 + 1) / 2 + t.2.2 * (2 * t.2.2 - 1) = n).card

/-- Sun's conjecture: `a n > 0` for all `n`, and `a n = 1` exactly for
`n ∈ {0, 5, 13, 14, 20, 112, 125}`. -/
theorem main :
    (∀ n : ℕ, 0 < a n) ∧ ∀ n : ℕ, a n = 1 ↔ n ∈ ({0, 5, 13, 14, 20, 112, 125} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a254668
