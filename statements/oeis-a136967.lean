import Mathlib

/-!
# A136967: Numbers k such that k and k^2 use only the digits 1, 2, 3 and 4

Source: https://oeis.org/A136967
Credit: @niclorusso

Conjecture (in the comments of A136967): No further terms up to 444444444444. Conjecture: these are
all the terms. The listed terms are 1, 2, 11, 12, 21, 111, 1111.

Conventions:
* The terms are the positive integers k such that every decimal digit of k and of k^2
  (`Nat.digits 10`) is one of 1, 2, 3, 4.
* "these are all the terms" is stated as a set equality with the listed terms.
-/

namespace OMA.S_oeis_a136967

/-- Every decimal digit of `x` is one of `1, 2, 3, 4`. -/
def UsesDigits (x : ℕ) : Prop :=
  ∀ d ∈ Nat.digits 10 x, d ∈ ({1, 2, 3, 4} : Finset ℕ)

/-- The conjecture on A136967: the positive `k` such that `k` and `k^2` use only the digits
`1, 2, 3, 4` are exactly `1, 2, 11, 12, 21, 111, 1111`. -/
theorem main :
    {k : ℕ | 0 < k ∧ UsesDigits k ∧ UsesDigits (k ^ 2)} = {1, 2, 11, 12, 21, 111, 1111} := by
  sorry

end OMA.S_oeis_a136967
