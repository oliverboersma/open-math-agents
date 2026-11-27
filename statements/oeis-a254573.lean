import Mathlib

/-!
# A254573: Number of ways to write n = x*(x+1) + y*(3*y+1)/2 + z*(3*z-1)/2 with x,y,z nonnegative integers.

Source: https://oeis.org/A254573
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A254573): `a(n) > 0` for all `n`. Also, `a(n) = 1` only for
`n = 0, 1, 4, 6, 10, 11, 23`. (Verified for `n ≤ 10^7`; Sun proved the version with `x, y, z`
arbitrary integers.)

Formalization notes:
* `a n` counts ordered triples `(x, y, z)` of natural numbers; each coordinate of a solution is at
  most `n`, so counting inside `range (n + 1)` gives the full count.
* `y * (3 * y + 1) / 2` and `z * (3 * z - 1) / 2` in `ℕ` are the (second) pentagonal numbers
  (exact divisions).
* With this definition `a 0, ..., a 24` = 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 1, 1, 3, 3, 5, 2, 2, 2, 3,
  3, 4, 3, 4, 1, 4 (data of A254573), and the `n < 200` with `a n = 1` are 0, 1, 4, 6, 10, 11, 23.
-/

namespace OMA.S_oeis_a254573

/-- A254573(n): the number of `(x, y, z)` with `n = x(x+1) + y(3y+1)/2 + z(3z-1)/2`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun t =>
    t.1 * (t.1 + 1) + t.2.1 * (3 * t.2.1 + 1) / 2 + t.2.2 * (3 * t.2.2 - 1) / 2 = n).card

/-- Sun's conjecture: `a n > 0` for all `n`, and `a n = 1` exactly for `n ∈ {0, 1, 4, 6, 10, 11, 23}`. -/
theorem main :
    (∀ n : ℕ, 0 < a n) ∧ ∀ n : ℕ, a n = 1 ↔ n ∈ ({0, 1, 4, 6, 10, 11, 23} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a254573
