import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs

/-!
# An upper bound for the mean of decimal fractions formed from consecutive integers

Source: https://oeis.org/A276646 (OEIS Foundation, CC BY-SA 4.0).
For a positive integer k, writing the digits of k directly after the decimal point
means k / 10^(1 + floor(log_10 k)). The conjecture concerns the mean of these
exact fractions before the floor used to define the sequence itself.
-/

namespace OMA.S_oeis_a276646

def decimalFraction (k : ℕ) : ℚ := (k : ℚ) / 10^(Nat.log 10 k + 1)

theorem main : ∀ n : ℕ, 0 < n →
    (∑ i ∈ Finset.range n, decimalFraction (i+1)) / (n : ℚ) ≤ 11/20 := by
  sorry

end OMA.S_oeis_a276646
