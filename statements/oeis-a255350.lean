import Mathlib

/-!
# A255350: Number of ways to write n as a*(2a-1)+ b*(2b-1) + c*(2c+1) + d*(2d+1), where a,b,c,d are nonnegative integers with a <= b and c <= d.

Source: https://oeis.org/A255350
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A255350):
(i) `a(n) > 0` for all `n`, i.e. any nonnegative integer can be expressed as the sum of two
hexagonal numbers `x(2x-1)` and two second hexagonal numbers `x(2x+1)` (`x ≥ 0`);
(ii) each nonnegative integer can be written as the sum of two pentagonal numbers `x(3x-1)/2` and
two second pentagonal numbers `x(3x+1)/2` (`x ≥ 0`).
(Verified for `n` up to `10^7` and `10^6` respectively.)

Formalization notes:
* The order conditions `a ≤ b`, `c ≤ d` of the counting function do not affect existence.
* In `ℕ`, `a * (2 * a - 1)` and `x * (3 * x - 1) / 2` are the integers `a(2a-1)` and `x(3x-1)/2`
  (for `x = 0` both sides are `0`; `x(3x-1)` is even, so the division is exact).
* Counting representations with these definitions gives `a 0, ..., a 19` =
  1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 2, 2 (data of A255350), and every `n < 200`
  has a representation as in (ii).
-/

namespace OMA.S_oeis_a255350

/-- Sun's conjecture, parts (i) and (ii). -/
theorem main :
    (∀ n : ℕ, ∃ a b c d : ℕ,
        n = a * (2 * a - 1) + b * (2 * b - 1) + c * (2 * c + 1) + d * (2 * d + 1)) ∧
      (∀ n : ℕ, ∃ w x y z : ℕ,
        n = w * (3 * w - 1) / 2 + x * (3 * x - 1) / 2 + y * (3 * y + 1) / 2 + z * (3 * z + 1) / 2) := by
  sorry

end OMA.S_oeis_a255350
