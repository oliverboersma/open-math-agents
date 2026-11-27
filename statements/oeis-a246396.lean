import Mathlib

/-!
# A246396: Nonnegative integers k satisfying cos(k) <= 0 and cos(k+1) <= 0.

Source: https://oeis.org/A246396
Credit: @rorcores

The entry (offset 0, data 2, 3, 8, 9, 15, 16, 21, 22, 27, 28, 33, 34, 35, 40, 41, ...) records in
its COMMENTS section:

  Conjecture: every term t has at least one neighbor which is equal to t plus or minus one.
  - Harvey P. Dale, Jul 11 2023

Conventions:
* A nonnegative integer `k` is a term when `cos k ≤ 0` and `cos (k + 1) ≤ 0` (real cosine,
  argument in radians).
* The sequence lists its terms in increasing order, so the neighbors of a term `t` are the terms
  just before and just after it in that order. A neighbor equals `t + 1` exactly when `t + 1` is
  a term, and a neighbor equals `t - 1` exactly when `1 ≤ t` and `t - 1` is a term (integers
  strictly between two consecutive terms are not terms).
-/

namespace OMA.S_oeis_a246396

/-- `k` is a term of A246396: `cos k ≤ 0` and `cos (k + 1) ≤ 0`. -/
def IsTerm (k : ℕ) : Prop := Real.cos (k : ℝ) ≤ 0 ∧ Real.cos ((k : ℝ) + 1) ≤ 0

/-- Dale's conjecture: every term `t` has a neighboring term equal to `t + 1` or to `t - 1`. -/
theorem main : ∀ t : ℕ, IsTerm t → IsTerm (t + 1) ∨ (1 ≤ t ∧ IsTerm (t - 1)) := by
  sorry

end OMA.S_oeis_a246396
