import Mathlib

/-!
# A137051: Numbers k such that k and k^2 use only the digits 1, 4, 5, 8 and 9

Source: https://oeis.org/A137051
Credit: @niclorusso

Conjecture (in the comments of A137051): The only squares present in the sequence are 1, 9, and
441.

Conventions:
* The terms are the positive integers k such that every decimal digit of k and of k^2
  (`Nat.digits 10`) is one of 1, 4, 5, 8, 9.
* "The only squares present" is stated as a set equality: the terms that are perfect squares are
  exactly 1, 9 and 441.
-/

namespace OMA.S_oeis_a137051

/-- Every decimal digit of `x` is one of `1, 4, 5, 8, 9`. -/
def UsesDigits (x : ℕ) : Prop :=
  ∀ d ∈ Nat.digits 10 x, d ∈ ({1, 4, 5, 8, 9} : Finset ℕ)

/-- `k` is a term of A137051. -/
def IsTerm (k : ℕ) : Prop :=
  0 < k ∧ UsesDigits k ∧ UsesDigits (k ^ 2)

/-- The conjecture on A137051: the square terms are exactly `1`, `9` and `441`. -/
theorem main : {k : ℕ | IsTerm k ∧ IsSquare k} = {1, 9, 441} := by
  sorry

end OMA.S_oeis_a137051
