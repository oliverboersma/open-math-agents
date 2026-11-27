import Mathlib

/-!
# A177680: Numbers n such that 6n and 12n are both the average of twin prime pairs.

Source: https://oeis.org/A177680
Credit: @rorcores

The entry (offset 1, data 1, 5, 110, 135, 355, 425, 555, 565, 975, 1045, ...) records in its
COMMENTS section:

  Conjecture: all terms but the first term are multiples of 5. - Harvey P. Dale, Sep 26 2017

Conventions:
* A number `m` is the average of a twin prime pair when there is a prime `p` with `p + 2` prime
  and `p + 1 = m` (the pair is `(m - 1, m + 1)`).
* A number `n` is a term when `6 * n` and `12 * n` are both averages of twin prime pairs, that is
  when `6 n - 1`, `6 n + 1`, `12 n - 1`, `12 n + 1` are all prime (as in the entry's example and
  Mathematica program).
* The sequence lists its terms in increasing order and its first term is `1`
  (`5, 7, 11, 13` are prime; `n = 0` is not a term). So "all terms but the first term" is
  "every term `n` with `n ≠ 1`".
-/

namespace OMA.S_oeis_a177680

/-- `m` is the average of a twin prime pair `(p, p + 2)`. -/
def IsTwinAverage (m : ℕ) : Prop := ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ p + 1 = m

/-- `n` is a term of A177680: `6 * n` and `12 * n` are both the average of twin prime pairs. -/
def IsTerm (n : ℕ) : Prop := IsTwinAverage (6 * n) ∧ IsTwinAverage (12 * n)

/-- Dale's conjecture: every term other than the first term `1` is a multiple of `5`. -/
theorem main : ∀ n : ℕ, IsTerm n → n ≠ 1 → 5 ∣ n := by
  sorry

end OMA.S_oeis_a177680
