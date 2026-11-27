import Mathlib

/-!
# A256171: Number of ways to write n as the sum of three unordered generalized heptagonal numbers.

Source: https://oeis.org/A256171
Credit: @divmxnd0x

The generalized `m`-gonal numbers are `((m - 2) k^2 - (m - 4) k) / 2` for `k ∈ ℤ`; for `m = 7`
these are the generalized heptagonal numbers `k(5k - 3)/2`.

Conjecture (Zhi-Wei Sun, stated in A256171):
(i) `a(n) > 0` except for `n = 10, 16, 76, 307`, i.e. a natural number is a sum of three
generalized heptagonal numbers if and only if it is not 10, 16, 76 or 307 (R. K. Guy noted in 1994
that 10, 16 and 76 are not such sums);
(ii) for any integer `m > 2` not divisible by 4, each sufficiently large integer `n` can be written
as the sum of three generalized `m`-gonal numbers.

Formalization notes:
* `(m - 2) k^2 - (m - 4) k = (m - 2) k (k - 1) + 2k` is even, so the division by 2 in `ℤ` is exact.
* With this definition the `n < 400` that are not sums of three generalized heptagonal numbers are
  exactly 10, 16, 76, 307.
-/

namespace OMA.S_oeis_a256171

/-- The `k`-th generalized `m`-gonal number, `k ∈ ℤ`. -/
def genPolygonal (m : ℕ) (k : ℤ) : ℤ :=
  (((m : ℤ) - 2) * k ^ 2 - ((m : ℤ) - 4) * k) / 2

/-- Sun's conjecture, parts (i) and (ii). -/
theorem main :
    (∀ n : ℕ, (∃ x y z : ℤ, (n : ℤ) = genPolygonal 7 x + genPolygonal 7 y + genPolygonal 7 z) ↔
        n ∉ ({10, 16, 76, 307} : Finset ℕ)) ∧
      ∀ m : ℕ, 2 < m → ¬ 4 ∣ m → ∀ᶠ n : ℕ in Filter.atTop,
        ∃ x y z : ℤ, (n : ℤ) = genPolygonal m x + genPolygonal m y + genPolygonal m z := by
  sorry

end OMA.S_oeis_a256171
