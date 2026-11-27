import Mathlib

/-!
# A257162: Number of ordered ways to write n as floor(x/5) + floor(y/6) + floor(z/7), where x is a pentagonal number, y is a hexagonal number and z is a heptagonal number.

Source: https://oeis.org/A257162
Credit: @divmxnd0x

The `i`-gonal numbers are `P_i(a) = ((i - 2) a^2 - (i - 4) a)/2` for `a = 0, 1, 2, ...`.

Conjecture (Zhi-Wei Sun, stated in A257162): `a(n) > 0` for all `n`. Moreover, for any
`i, j, k = 3, 4, 5, ...` all sufficiently large integers can be written as
`floor(x/i) + floor(y/j) + floor(z/k)`, where `x` is an `i`-gonal number, `y` is a `j`-gonal number
and `z` is a `k`-gonal number.

Formalization notes:
* `P_i(a)` is computed in `ℕ` as `(i - 2) * (a * (a - 1) / 2) + a`, which equals
  `((i - 2) a^2 - (i - 4) a)/2` for every `i ≥ 2` (the product `a (a - 1)` is even).
* `floor(x/i)` for natural numbers is natural-number division.
* The polygonal numbers include `P_i(0) = 0`: with `a ≥ 0` the number of ordered representations
  for `n = 0, ..., 9` is 8, 12, 18, 13, 21, 15, 16, 18, 21, 18, matching the data of A257162
  (with `a ≥ 1` it would be 1, 3, 6, ...).
-/

namespace OMA.S_oeis_a257162

/-- The `a`-th `i`-gonal number. -/
def polygonal (i a : ℕ) : ℕ :=
  (i - 2) * (a * (a - 1) / 2) + a

/-- Sun's conjecture, both parts. -/
theorem main :
    (∀ n : ℕ, ∃ a b c : ℕ, n = polygonal 5 a / 5 + polygonal 6 b / 6 + polygonal 7 c / 7) ∧
      ∀ i j k : ℕ, 3 ≤ i → 3 ≤ j → 3 ≤ k → ∀ᶠ n : ℕ in Filter.atTop,
        ∃ a b c : ℕ, n = polygonal i a / i + polygonal j b / j + polygonal k c / k := by
  sorry

end OMA.S_oeis_a257162
