import Mathlib

/-!
# A187757: Number of ways to write n=x+y (x,y>0) with 6x-1, 6x+1, 6y+1 and 6y+5 all prime

Source: https://oeis.org/A187757
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A187757): a(n)>0 for all n>1.

Conventions:
* x, y are positive integers; 6x - 1 >= 5, so the natural-number subtraction is exact.
* a(n) > 0 means that at least one such pair (x, y) exists.
-/

namespace OMA.S_oeis_a187757

/-- Sun's conjecture on A187757: every `n > 1` is `x + y` with `x, y > 0` such that `6x - 1`,
`6x + 1`, `6y + 1` and `6y + 5` are all prime. -/
theorem main : ∀ n : ℕ, 1 < n → ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
    (6 * x - 1).Prime ∧ (6 * x + 1).Prime ∧ (6 * y + 1).Prime ∧ (6 * y + 5).Prime := by
  sorry

end OMA.S_oeis_a187757
