import Mathlib

/-!
# A036937: Smallest n-digit prime containing only digits 2 and 3

Source: https://oeis.org/A036937
Credit: @niclorusso

Conjecture (in the comments of A036937): It is conjectured that such a prime exists for every value
of n.

Conventions:
* n ranges over the positive integers (offset 1). An n-digit number has exactly n decimal digits:
  `(Nat.digits 10 p).length = n`.
* "containing only digits 2 and 3": every decimal digit of p is 2 or 3 (as in the data, e.g.
  a(1) = 2, a(4) = 2333; both digits need not occur).
-/

namespace OMA.S_oeis_a036937

/-- The conjecture on A036937: for every `n >= 1` there is an `n`-digit prime all of whose decimal
digits are `2` or `3`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ (Nat.digits 10 p).length = n ∧
    ∀ d ∈ Nat.digits 10 p, d = 2 ∨ d = 3 := by
  sorry

end OMA.S_oeis_a036937
