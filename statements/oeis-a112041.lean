import Mathlib

/-!
# A112041: Numbers k such that 1*k + 1, 3*k + 1, 9*k + 1, 27*k + 1 are all primes.

Source: https://oeis.org/A112041
Credit: @rorcores

The entry (offset 1, data 4, 60, 180, 760, 910, 1020, 1230, 1600, ...) records in its COMMENTS
section:

  Conjecture: all terms except the first are multiples of 10. - Harvey P. Dale, Mar 26 2015

Conventions:
* A number `k` is a term when `k + 1`, `3 * k + 1`, `9 * k + 1` and `27 * k + 1` are all prime.
* The sequence lists its terms in increasing order and its first term is `4`
  (`5, 13, 37, 109` are prime, while `k = 0, 1, 2, 3` fail: `1`, `4`, `55` and `4` are not prime).
  So "all terms except the first" is "every term `k` with `k ≠ 4`".
-/

namespace OMA.S_oeis_a112041

/-- `k` is a term of A112041: `k + 1`, `3 * k + 1`, `9 * k + 1` and `27 * k + 1` are all prime. -/
def IsTerm (k : ℕ) : Prop :=
  (1 * k + 1).Prime ∧ (3 * k + 1).Prime ∧ (9 * k + 1).Prime ∧ (27 * k + 1).Prime

/-- Dale's conjecture: every term other than the first term `4` is a multiple of `10`. -/
theorem main : ∀ k : ℕ, IsTerm k → k ≠ 4 → 10 ∣ k := by
  sorry

end OMA.S_oeis_a112041
