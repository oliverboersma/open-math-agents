import Mathlib

/-!
# A256132: Number of ways to write n as w*(3w+1)/2 + x*(3x-1)/2 + y*(3y-1)/2 + z*(3z-1)/2, where w,x,y,z are nonnegative integers with x <= y <= z.

Source: https://oeis.org/A256132
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A256132): `a(n) > 0` for all `n`, i.e. any nonnegative integer
`n` can be expressed as the sum of three pentagonal numbers `x(3x-1)/2` and a second pentagonal
number `w(3w+1)/2` (`w, x, y, z ≥ 0`).

Formalization notes:
* The order condition `x ≤ y ≤ z` of the counting function does not affect existence.
* `x * (3 * x - 1) / 2` in `ℕ` is the pentagonal number (`x(3x-1)` is even; for `x = 0` it is `0`).
* Counting representations with these definitions gives `a 0, ..., a 19` =
  1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2, 1, 3, 3, 3, 3, 2, 4, 3, 2 (data of A256132).
-/

namespace OMA.S_oeis_a256132

/-- Sun's conjecture: every `n` is a second pentagonal number plus three pentagonal numbers. -/
theorem main : ∀ n : ℕ, ∃ w x y z : ℕ,
    n = w * (3 * w + 1) / 2 + x * (3 * x - 1) / 2 + y * (3 * y - 1) / 2 + z * (3 * z - 1) / 2 := by
  sorry

end OMA.S_oeis_a256132
