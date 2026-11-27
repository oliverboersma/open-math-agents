import Mathlib

/-!
# A382437: a(n) = a(n-1)^2 + 4 * a(n-1), with a(0) = 2.

Source: https://oeis.org/A382437
Credit: @canneyi

Conjecture (in the entry):
`a(n) = Sum_{k=1..2^n} (2^n * 2^k * binomial(2^n + k - 1, 2*k - 1) / k)`.

Formalization notes:
* Offset 0, as in the entry (data: 2, 12, 192, 37632, ...).
* The sum is taken in `ℚ`, so `/ k` is exact division of rational numbers.
* `2 ^ n + k - 1` and `2 * k - 1` are natural numbers; `k ≥ 1` in the sum, so the subtractions
  are exact.
-/

namespace OMA.S_oeis_a382437

/-- `a(n) = a(n-1)^2 + 4 * a(n-1)`, with `a(0) = 2`. -/
def a : ℕ → ℕ
  | 0 => 2
  | n + 1 => a n ^ 2 + 4 * a n

theorem main : ∀ n : ℕ,
    (a n : ℚ) = ∑ k ∈ Finset.Icc 1 (2 ^ n),
      (2 : ℚ) ^ n * 2 ^ k * (Nat.choose (2 ^ n + k - 1) (2 * k - 1) : ℚ) / (k : ℚ) := by
  sorry

end OMA.S_oeis_a382437
