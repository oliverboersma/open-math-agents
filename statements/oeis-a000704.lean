import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-! Mathar's recurrence for the number of even involutions, OEIS A000704. -/

namespace OMA.S_oeis_a000704

open Finset

/-- The count of involutions on `n` labels with exactly `k` transpositions. -/
def matchings (n k : ℕ) : ℕ :=
  n.choose (2 * k) * (2 * k - 1).doubleFactorial

/-- The binomial and double factorial formula for A000704. -/
def a (n : ℕ) : ℕ := ∑ j ∈ range (n / 4 + 1), matchings n (2 * j)

theorem main : ∀ n : ℕ, 5 ≤ n →
    (a n : ℤ) - 3 * a (n - 1) + 3 * a (n - 2) - a (n - 3) -
      ((n : ℤ) - 1) * ((n : ℤ) - 3) * a (n - 4) +
        ((n : ℤ) - 3) * ((n : ℤ) - 4) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a000704
