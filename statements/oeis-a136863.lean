import Mathlib

/-!
# A136863: Numbers k such that k and k^2 use only the digits 0, 1, 4 and 7

Source: https://oeis.org/A136863
Credit: @niclorusso

Conjecture (Robert Israel, Jun 05 2025, in the comments of A136863): the only terms not ending in 0
are 1 and 1071.

Conventions:
* k is a term when every decimal digit of k and of k^2 (`Nat.digits 10`) is 0, 1, 4 or 7.
* "not ending in 0" means not divisible by 10 (this also excludes the term 0).
* The conjecture is stated as a set equality.
-/

namespace OMA.S_oeis_a136863

/-- Every decimal digit of `x` is `0, 1, 4` or `7`. -/
def UsesDigits (x : ℕ) : Prop :=
  ∀ d ∈ Nat.digits 10 x, d ∈ ({0, 1, 4, 7} : Finset ℕ)

/-- Israel's conjecture on A136863: the terms not ending in `0` are exactly `1` and `1071`. -/
theorem main : {k : ℕ | UsesDigits k ∧ UsesDigits (k ^ 2) ∧ ¬ 10 ∣ k} = {1, 1071} := by
  sorry

end OMA.S_oeis_a136863
