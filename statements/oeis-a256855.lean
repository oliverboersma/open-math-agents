import Mathlib

/-!
# A256855: Number of ordered ways to write n as x*(3*x-1)/2 + y*(3*y+1)/2 + z*(3*z+1), where x and y are nonnegative integers and z is an integer.

Source: https://oeis.org/A256855
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A256855): `a(n) > 0` for all `n`. Also, any nonnegative integer
can be written as `x(3x-1)/2 + y(3y-1) + z(3z+1)/2` with `x, y` nonnegative integers and `z` an
integer, and each `n = 0, 1, 2, ...` can be expressed as `x(3x+1)/2 + 3y(3y+1)/2 + z(3z+1)/2` with
`x, y` nonnegative integers and `z` an integer.

Formalization notes:
* All three representations are stated in `ℤ`, with `x, y` natural numbers cast to `ℤ` and `z`
  an integer; each numerator `t(3t ± 1)` is even, so the divisions by 2 are exact.
* With this definition the number of ordered representations of the first kind for
  `n = 0, ..., 19` is 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 2, 3, 4, 1, 4, 3, 5, 4, 3, 3 (data of A256855),
  and every `n < 300` has representations of the second and third kinds.
-/

namespace OMA.S_oeis_a256855

/-- Sun's three conjectures of A256855. -/
theorem main :
    (∀ n : ℕ, ∃ x y : ℕ, ∃ z : ℤ,
        (n : ℤ) = (x : ℤ) * (3 * x - 1) / 2 + (y : ℤ) * (3 * y + 1) / 2 + z * (3 * z + 1)) ∧
      (∀ n : ℕ, ∃ x y : ℕ, ∃ z : ℤ,
        (n : ℤ) = (x : ℤ) * (3 * x - 1) / 2 + (y : ℤ) * (3 * y - 1) + z * (3 * z + 1) / 2) ∧
      ∀ n : ℕ, ∃ x y : ℕ, ∃ z : ℤ,
        (n : ℤ) = (x : ℤ) * (3 * x + 1) / 2 + 3 * (y : ℤ) * (3 * y + 1) / 2 + z * (3 * z + 1) / 2 := by
  sorry

end OMA.S_oeis_a256855
