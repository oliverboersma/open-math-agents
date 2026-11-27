import Mathlib

/-!
# A254661: Number of ways to write n as the sum of a triangular number, an even square and a second pentagonal number.

Source: https://oeis.org/A254661
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A254661):
(i) `a(n) > 0` for all `n`. Also, `a(n) = 1` only for
`n = 0, 1, 2, 4, 9, 11, 13, 20, 35, 69, 75, 188`.
(ii) For each `a = 2, 3`, any nonnegative integer `n` can be written as
`x(x+1)/2 + a*y^2 + z(3z+1)/2` with `x, y, z` nonnegative integers.

Formalization notes:
* `a n` counts ordered triples `(x, y, z)` of natural numbers with
  `n = x(x+1)/2 + (2y)^2 + z(3z+1)/2`; each coordinate of a solution is at most `n`, so counting
  inside `range (n + 1)` gives the full count.
* With this definition `a 0, ..., a 24` = 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 1, 3, 1, 2, 2, 3, 4, 2,
  4, 1, 5, 3, 2, 2 (data of A254661), and the `n < 250` with `a n = 1` are exactly the listed ones.
-/

namespace OMA.S_oeis_a254661

/-- A254661(n): the number of `(x, y, z)` with `n = x(x+1)/2 + (2y)^2 + z(3z+1)/2`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun t =>
    t.1 * (t.1 + 1) / 2 + (2 * t.2.1) ^ 2 + t.2.2 * (3 * t.2.2 + 1) / 2 = n).card

/-- Sun's conjecture, parts (i) and (ii). -/
theorem main :
    (∀ n : ℕ, 0 < a n) ∧
      (∀ n : ℕ, a n = 1 ↔ n ∈ ({0, 1, 2, 4, 9, 11, 13, 20, 35, 69, 75, 188} : Finset ℕ)) ∧
      ∀ c ∈ ({2, 3} : Finset ℕ), ∀ n : ℕ, ∃ x y z : ℕ,
        n = x * (x + 1) / 2 + c * y ^ 2 + z * (3 * z + 1) / 2 := by
  sorry

end OMA.S_oeis_a254661
