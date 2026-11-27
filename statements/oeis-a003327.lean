import Mathlib

/-!
# A003327: Numbers that are the sum of 4 positive cubes in 1 or more way.

Source: https://oeis.org/A003327
Credit: @ShoQo

Conjecture (OEIS comment, Charles R Greathouse IV, Jan 14 2017; from Deshouillers, Hennecart,
Landreau, "7373170279850", Math. Comp. 69 (2000), 421-439): every number greater than
7373170279850 is in this sequence.

Formalization notes:
* "Positive cubes" means `a ^ 3` with `a ≥ 1`; the four cubes need not be distinct
  (the data contains 4 = 1 + 1 + 1 + 1).
* Membership in the sequence is exactly `IsSumOfFourPositiveCubes`; the ordering of the
  sequence plays no role in the conjecture.
-/

namespace OMA.S_oeis_a003327

/-- `n` is a sum of four positive cubes (repetitions allowed). -/
def IsSumOfFourPositiveCubes (n : ℕ) : Prop :=
  ∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ n = a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3

theorem main : ∀ n : ℕ, 7373170279850 < n → IsSumOfFourPositiveCubes n := by
  sorry

end OMA.S_oeis_a003327
