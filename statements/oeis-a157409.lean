import Mathlib

/-!
# A157409: Minimum of { k > 0 : [2^n / 3^k] mod 6 = 3 } if such k exists, 0 otherwise

Source: https://oeis.org/A157409
Credit: @niclorusso

Conjecture (in the comments of A157409): a(n) = 0 only for n in {0,1,2,3,4,7,9,10,14,15,17,26}.

Conventions:
* The sequence has offset 0. [x] is the floor, so [2^n / 3^k] is the natural-number quotient
  `2 ^ n / 3 ^ k`, and "mod 6" is `% 6`.
* a(n) = 0 exactly when no k > 0 has [2^n / 3^k] mod 6 = 3.
* "a(n) = 0 only for n in {...}" is stated as a set equality: a(n) = 0 holds exactly for these
  twelve values of n.
-/

namespace OMA.S_oeis_a157409

/-- The conjecture on A157409: the `n` for which no `k > 0` has `[2^n / 3^k] mod 6 = 3` are exactly
`0, 1, 2, 3, 4, 7, 9, 10, 14, 15, 17, 26`. -/
theorem main :
    {n : ℕ | ¬ ∃ k : ℕ, 0 < k ∧ 2 ^ n / 3 ^ k % 6 = 3} =
      {0, 1, 2, 3, 4, 7, 9, 10, 14, 15, 17, 26} := by
  sorry

end OMA.S_oeis_a157409
