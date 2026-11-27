import Mathlib

/-!
# A057015: Numbers k such that k^2 + 1, k^2 + 3, k^2 + 7 and k^2 + 9 are all primes

Source: https://oeis.org/A057015
Credit: @xor2k

Formalizes the OEIS A057015 conjecture: all terms after the first term are equal to zero mod 10.

Conventions: `k` ranges over the natural numbers and is a term when `k^2 + 1`, `k^2 + 3`,
`k^2 + 7` and `k^2 + 9` are all prime (`Nat.Prime`). The first term of the sequence is `2`
(`0` and `1` are not terms), so the terms after the first term are exactly the terms `k > 2`.
Zero mod 10 is expressed as `k % 10 = 0`.
-/

namespace OMA.S_oeis_a057015

/-- `k` is a term of A057015: `k^2 + 1`, `k^2 + 3`, `k^2 + 7` and `k^2 + 9` are all prime. -/
def IsTerm (k : ℕ) : Prop :=
  (k ^ 2 + 1).Prime ∧ (k ^ 2 + 3).Prime ∧ (k ^ 2 + 7).Prime ∧ (k ^ 2 + 9).Prime

/-- Every term greater than the first term `2` is congruent to `0` mod `10`. -/
theorem main :
    ∀ k : ℕ, IsTerm k → 2 < k → k % 10 = 0 := by
  sorry

end OMA.S_oeis_a057015
