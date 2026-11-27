import Mathlib

/-!
# OEIS A037301: consecutive integers with equal binary and ternary digit sums

Thomas König conjectured on August 15, 2020 that A037301 contains no run of
five consecutive integers. The entry gives 10, 11, 12, 13 as a run of four.
The sequence includes zero. Its membership condition uses ordinary positional
digits, whose sum is independent of the order in which they are listed.

Source: https://oeis.org/A037301
-/

namespace OMA.S_oeis_a037301

def equalDigitSums (n : ℕ) : Prop :=
  (Nat.digits 2 n).sum = (Nat.digits 3 n).sum

theorem main :
    (∀ n : ℕ, ¬ (∀ i : ℕ, i < 5 → equalDigitSums (n + i))) ∧
    (∀ i : ℕ, i < 4 → equalDigitSums (10 + i)) := by
  sorry

end OMA.S_oeis_a037301
