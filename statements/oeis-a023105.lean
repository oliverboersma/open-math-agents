import Mathlib

/-!
# A023105: Number of distinct quadratic residues mod 2^n.

Source: https://oeis.org/A023105
Credit: @ShoQo

Conjecture (Tilman Neumann, Sep 20 2020): a(n) = 2 + (the number of A004215 entries < 2^n),
for n>0.

Formalization notes:
* a(n) counts the distinct values of `x^2 mod 2^n` (0 included, offset 0: 1, 2, 2, 3, 4, 7,
  12, ...), stated as the number of distinct values of `x^2 % 2^n` for `0 ≤ x < 2^n`.
* A004215 is "numbers that are the sum of 4 but no fewer nonzero squares", stated literally:
  a sum of 4 nonzero squares and not a sum of 1, 2 or 3 nonzero squares.
* Checked numerically for 1 ≤ n ≤ 20.
-/

namespace OMA.S_oeis_a023105

/-- a(n): the number of distinct quadratic residues modulo `2 ^ n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (2 ^ n)).image (fun x => x ^ 2 % 2 ^ n)).card

/-- Membership in A004215: `m` is a sum of 4 but no fewer nonzero squares. -/
def InA004215 (m : ℕ) : Prop :=
  (∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ m = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ∧
  (¬ ∃ a : ℕ, 0 < a ∧ m = a ^ 2) ∧
  (¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ m = a ^ 2 + b ^ 2) ∧
  (¬ ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ m = a ^ 2 + b ^ 2 + c ^ 2)

theorem main :
    ∀ n : ℕ, 0 < n → a n = 2 + {m : ℕ | m < 2 ^ n ∧ InA004215 m}.ncard := by
  sorry

end OMA.S_oeis_a023105
