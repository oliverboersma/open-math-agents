import Mathlib

/-!
# A230168: Primes of the form 45 * 2^n - 1

Source: https://oeis.org/A230168
Credit: @AkiRA-COM-FP

Formalizes the OEIS A230168 conjecture: every prime of the form `45 * 2^n - 1` ends in the
decimal digit `9`.
-/

namespace OMA.S_oeis_a230168

/-- Every prime of the form `45 * 2^n - 1` is congruent to `9` modulo `10`. -/
theorem main :
    ∀ n : ℕ, (45 * 2 ^ n - 1).Prime → (45 * 2 ^ n - 1) % 10 = 9 := by
  sorry

end OMA.S_oeis_a230168
