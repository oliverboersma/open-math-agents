import Mathlib

/-!
# A005479: Prime Lucas numbers (cf. A000032)

Source: https://oeis.org/A005479
Credit: @niclorusso

Conjectures (in the comments of A005479): 7, 47 and 2207 are the only a(n) mod 10 = 7. They are
also the only a(n) values where the Lucas index is not a prime.

Conventions:
* Lucas numbers (A000032): L(0) = 2, L(1) = 1, L(k+2) = L(k+1) + L(k). The terms of A005479 are the
  prime values of L.
* The Lucas index of a term p is the k with L(k) = p (it is unique for p > 1). The indices of the
  prime Lucas numbers are A001606: 0, 2, 4, 5, 7, 8, 11, 13, 16, 17, ...
* The second conjecture is read for indices k >= 1: the term 2 = L(0) has index 0, which is not a
  prime either, and the comment plainly does not mean it (it names only 7, 47 and 2207, with indices
  4, 8 and 16).
* Both conjectures are stated, as set equalities, joined by `∧`.
-/

namespace OMA.S_oeis_a005479

/-- The Lucas numbers: `L 0 = 2`, `L 1 = 1`, `L (k + 2) = L (k + 1) + L k`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | k + 2 => lucas (k + 1) + lucas k

/-- The two conjectures on A005479: the prime Lucas numbers congruent to 7 mod 10 are exactly 7, 47
and 2207, and these are also exactly the prime Lucas numbers `L k` with `k >= 1` not prime. -/
theorem main :
    {p : ℕ | (∃ k : ℕ, lucas k = p) ∧ p.Prime ∧ p % 10 = 7} = {7, 47, 2207} ∧
      {p : ℕ | ∃ k : ℕ, 1 ≤ k ∧ ¬ k.Prime ∧ lucas k = p ∧ p.Prime} = {7, 47, 2207} := by
  sorry

end OMA.S_oeis_a005479
