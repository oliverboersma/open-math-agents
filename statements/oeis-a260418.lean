import Mathlib

/-!
# A260418: Number of ways to write 12*n+5 as 4*x^4 + 4*y^2 + z^2, where x is a nonnegative integer, and y and z are positive integers.

Source: https://oeis.org/A260418
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A260418):
(i) `a(n) > 0` for all `n = 0, 1, 2, ...`, and `a(n) = 1` only for
`n = 0, 4, 54, 159, 289, 999, 1175, 1404, 16391, 39688`.
(ii) All the numbers `24n + 4` (`n = 0, 1, 2, ...`) can be written as `3x^4 + 24y^2 + z^2`, where
`x, y, z` are integers with `x > 0` and `z > 0`.
(iii) All the numbers `24n + 13` (`n = 0, 1, 2, ...`) can be written as `3x^4 + 9y^2 + z^2` with
`x, y, z` positive integers.

Formalization notes:
* `a n` counts triples `(x, y, z)` with `x ≥ 0`, `y, z ≥ 1`; each coordinate of a solution is at
  most `12n + 5`, so counting inside `range (12n + 6)` gives the full count.
* In (ii), `y` ranges over all integers (only `x` and `z` are required to be positive).
* With this definition `a 0, ..., a 19` = 1, 2, 2, 2, 1, 3, 2, 4, 3, 2, 3, 2, 5, 2, 3, 3, 2, 4, 3, 3
  (data of A260418), and the `n < 1500` with `a n ≤ 1` are 0, 4, 54, 159, 289, 999, 1175, 1404.
-/

namespace OMA.S_oeis_a260418

/-- A260418(n): the number of `(x, y, z)`, `x ≥ 0`, `y, z ≥ 1`, with `12n + 5 = 4x^4 + 4y^2 + z^2`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (12 * n + 6) ×ˢ Finset.range (12 * n + 6) ×ˢ Finset.range (12 * n + 6)).filter
    fun t => 1 ≤ t.2.1 ∧ 1 ≤ t.2.2 ∧ 12 * n + 5 = 4 * t.1 ^ 4 + 4 * t.2.1 ^ 2 + t.2.2 ^ 2).card

/-- Sun's conjecture, parts (i), (ii) and (iii). -/
theorem main :
    (∀ n : ℕ, 0 < a n) ∧
      (∀ n : ℕ, a n = 1 ↔
        n ∈ ({0, 4, 54, 159, 289, 999, 1175, 1404, 16391, 39688} : Finset ℕ)) ∧
      (∀ n : ℕ, ∃ x y z : ℤ, 0 < x ∧ 0 < z ∧ (24 * n + 4 : ℤ) = 3 * x ^ 4 + 24 * y ^ 2 + z ^ 2) ∧
      ∀ n : ℕ, ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ 24 * n + 13 = 3 * x ^ 4 + 9 * y ^ 2 + z ^ 2 := by
  sorry

end OMA.S_oeis_a260418
