import Mathlib

/-!
# A254629: Number of ways to write n as x^2 + y*(y+1) + z*(4*z+1) with x,y,z nonnegative integers.

Source: https://oeis.org/A254629
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A254629):
(i) `a(n) > 0` for all `n`, and `a(n) > 1` for all `n > 338`.
(ii) If `f(x)` is one of the polynomials `3x^2+x`, `(7x^2+3x)/2`, `(9x^2-x)/2`, `(11x^2-7x)/2`,
`(15x^2-7x)/2`, `(15x^2-11x)/2`, then any nonnegative integer `n` can be written as
`x^2 + y(y+1) + f(z)` with `x, y, z` nonnegative integers.
(Sun proved that every `n` is `x^2 + y(y+1) + z(4z+1)` with integers `x, y, z`.)

Formalization notes:
* `a n` counts ordered triples `(x, y, z)` of natural numbers; each coordinate of a solution is at
  most `n`, so counting inside `range (n + 1)` gives the full count.
* For natural `z` the six polynomial values are natural numbers: each numerator is `z (c z ± d)`
  with `c z ± d ≥ 0` for `z ≥ 1` and of even parity overall, so the divisions by 2 are exact and
  the truncated subtractions in `ℕ` are the integer ones.
* With these definitions `a 0, ..., a 19` = 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 1, 2, 3, 1, 3,
  1 (data of A254629), the largest `n < 700` with `a n ≤ 1` is 338, and every `n < 500` is
  representable for each of the six polynomials.
-/

namespace OMA.S_oeis_a254629

/-- A254629(n): the number of `(x, y, z)` with `n = x^2 + y(y+1) + z(4z+1)`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun t =>
    t.1 ^ 2 + t.2.1 * (t.2.1 + 1) + t.2.2 * (4 * t.2.2 + 1) = n).card

/-- The six polynomials of part (ii). -/
def polys : List (ℕ → ℕ) :=
  [fun z => 3 * z ^ 2 + z, fun z => (7 * z ^ 2 + 3 * z) / 2, fun z => (9 * z ^ 2 - z) / 2,
    fun z => (11 * z ^ 2 - 7 * z) / 2, fun z => (15 * z ^ 2 - 7 * z) / 2,
    fun z => (15 * z ^ 2 - 11 * z) / 2]

/-- Sun's conjecture, parts (i) and (ii). -/
theorem main :
    (∀ n : ℕ, 0 < a n) ∧ (∀ n : ℕ, 338 < n → 1 < a n) ∧
      ∀ f ∈ polys, ∀ n : ℕ, ∃ x y z : ℕ, n = x ^ 2 + y * (y + 1) + f z := by
  sorry

end OMA.S_oeis_a254629
