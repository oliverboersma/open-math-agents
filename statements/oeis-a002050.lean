import Mathlib

/-!
# OEIS A002050: Eventual periodicity modulo a positive integer

Source: https://oeis.org/A002050
Credit: @gblacher2

Peter Bala conjectured that the sequence reduced modulo a positive integer
has an eventual period dividing Euler's totient of that integer.
-/

namespace OMA.S_oeis_a002050

/-- OEIS A000670. A partition into j nonempty blocks contributes j! orders. -/
def orderedBell (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), j.factorial * Nat.stirlingSecond n j

/-- The binomial sum of the ordered Bell numbers over the nonempty subsets. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, Nat.choose n k * orderedBell k

theorem main : ∀ m : ℕ, 0 < m →
    ∃ p N : ℕ, 0 < p ∧ p ∣ m.totient ∧
      ∀ n ≥ N, Nat.ModEq m (a (n + p)) (a n) := by
  sorry

end OMA.S_oeis_a002050
