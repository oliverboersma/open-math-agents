import Mathlib

/-!
# A187758: Number of ways to write n=x+y (x,y>0) with 2x-3, 2x+3, 6y+1 and 6y+5 all prime

Source: https://oeis.org/A187758
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A187758): a(n)>0 for all n>4.

Conventions:
* x, y are positive integers. For x = 1 the integer 2x - 3 = -1 is not prime; the natural-number
  subtraction gives 0, which is not prime either, so the condition is unchanged.
* a(n) > 0 means that at least one such pair (x, y) exists.
-/

namespace OMA.S_oeis_a187758

/-- Sun's conjecture on A187758: every `n > 4` is `x + y` with `x, y > 0` such that `2x - 3`,
`2x + 3`, `6y + 1` and `6y + 5` are all prime. -/
theorem main : ∀ n : ℕ, 4 < n → ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
    (2 * x - 3).Prime ∧ (2 * x + 3).Prime ∧ (6 * y + 1).Prime ∧ (6 * y + 5).Prime := by
  sorry

end OMA.S_oeis_a187758
