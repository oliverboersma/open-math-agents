import Mathlib

/-!
# A036229: Smallest n-digit prime containing only digits 1 or 2 or -1 if no such prime exists

Source: https://oeis.org/A036229
Credit: @niclorusso

Conjecture (in the comments of A036229): It is conjectured that such a prime always exists.

Conventions:
* n ranges over the positive integers (offset 1). An n-digit number has exactly n decimal digits:
  `(Nat.digits 10 p).length = n`.
* "containing only digits 1 or 2": every decimal digit of p is 1 or 2.
-/

namespace OMA.S_oeis_a036229

/-- The conjecture on A036229: for every `n >= 1` there is an `n`-digit prime all of whose decimal
digits are `1` or `2`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ (Nat.digits 10 p).length = n ∧
    ∀ d ∈ Nat.digits 10 p, d = 1 ∨ d = 2 := by
  sorry

end OMA.S_oeis_a036229
