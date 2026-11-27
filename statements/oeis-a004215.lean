import Mathlib

/-!
# A004215: Numbers that are the sum of 4 but no fewer nonzero squares.

Source: https://oeis.org/A004215
Credit: @ShoQo

Conjecture (Tilman Neumann, Sep 20 2020): The number of terms < 2^n is A023105(n) - 2.

Formalization notes:
* Membership in A004215 is stated literally: `m` is a sum of 4 nonzero squares and not a sum
  of 1, 2 or 3 nonzero squares.
* A023105(n) is the number of distinct quadratic residues mod 2^n (0 included, offset 0:
  1, 2, 2, 3, 4, 7, 12, ...), stated as the number of distinct values of `x^2 % 2^n` for
  `0 ≤ x < 2^n`.
* The source gives no range for n. At n = 0 the count is 0 while A023105(0) - 2 = -1, so the
  conjecture is stated for `n ≥ 1`, with the subtraction done in `ℤ`. Checked numerically for
  1 ≤ n ≤ 20.
-/

namespace OMA.S_oeis_a004215

/-- `m` is a sum of 4 but no fewer nonzero squares. -/
def InA004215 (m : ℕ) : Prop :=
  (∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ m = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ∧
  (¬ ∃ a : ℕ, 0 < a ∧ m = a ^ 2) ∧
  (¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ m = a ^ 2 + b ^ 2) ∧
  (¬ ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ m = a ^ 2 + b ^ 2 + c ^ 2)

/-- A023105(n): the number of distinct quadratic residues modulo `2 ^ n`. -/
def numQuadResiduesPowTwo (n : ℕ) : ℕ :=
  ((Finset.range (2 ^ n)).image (fun x => x ^ 2 % 2 ^ n)).card

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ({m : ℕ | m < 2 ^ n ∧ InA004215 m}.ncard : ℤ) = (numQuadResiduesPowTwo n : ℤ) - 2 := by
  sorry

end OMA.S_oeis_a004215
