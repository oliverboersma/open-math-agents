import Mathlib

/-!
# A230252: Number of ways to write n = x + y (x, y > 0) with 2*x + 1, x^2 + x + 1 and y^2 + y + 1 all prime

Source: https://oeis.org/A230252
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A230252): (i) a(n) > 0 for all n > 1.

(Only part (i) of the conjecture is formalized here.)

Conventions:
* x, y are positive integers; a(n) > 0 means that at least one such pair (x, y) exists.
-/

namespace OMA.S_oeis_a230252

/-- Sun's conjecture (i) on A230252: every `n > 1` is `x + y` with `x, y > 0` such that
`2x + 1`, `x^2 + x + 1` and `y^2 + y + 1` are all prime. -/
theorem main : ∀ n : ℕ, 1 < n → ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
    (2 * x + 1).Prime ∧ (x ^ 2 + x + 1).Prime ∧ (y ^ 2 + y + 1).Prime := by
  sorry

end OMA.S_oeis_a230252
