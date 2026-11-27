import Mathlib

/-!
# A117971: Position of the first 2 in the ternary expansion of 2^n, or 0 if there is none

Source: https://oeis.org/A117971
Credit: @niclorusso

A117971(n) is the one-based position of the first 2 from the least significant digit in the
ternary expansion of 2^n, or 0 if there are no 2's present.

Conjecture (in the comments of A117971): a(0), a(2) and a(8) are the conjectured to be the only
terms equal to 0.

Conventions:
* The sequence has offset 0. `Nat.digits 3 (2 ^ n)` lists the ternary digits of 2^n; a(n) = 0 means
  that none of them is 2.
* "the only terms equal to 0" is stated as a set equality: 2^n has no ternary digit 2 exactly for
  n = 0, 2, 8 (2^0 = 1, 2^2 = 4 = 11_3, 2^8 = 256 = 100111_3).
* This is the exact form of the question behind Erdős problem 406, whose formal-conjectures
  statement only asks for finiteness; here the exceptional set is pinned down.
-/

namespace OMA.S_oeis_a117971

/-- The conjecture on A117971: `2^n` has no digit `2` in base 3 exactly when `n` is `0`, `2` or
`8`. -/
theorem main : {n : ℕ | 2 ∉ Nat.digits 3 (2 ^ n)} = {0, 2, 8} := by
  sorry

end OMA.S_oeis_a117971
