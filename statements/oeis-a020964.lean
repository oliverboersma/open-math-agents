import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
Chai Wah Wu's recurrence and generating-function conjectures in OEIS A020964.
Source: https://oeis.org/A020964/internal

The sum starts at positive k, encoded with k+1 over the naturals.
The denominator is written with constant coefficient one by moving the
leading minus sign in the displayed OEIS quotient to the denominator.
-/

namespace OMA.S_oeis_a020964

open PowerSeries
open scoped PowerSeries

noncomputable def a (n : ℕ) : ℤ :=
  ∑' k : ℕ, ⌊3 * (1 + Real.sqrt 2) ^ ((n : ℤ) - ((k : ℤ) + 1))⌋

theorem main :
    (∀ n : ℕ, 6 < n → a n = 3 * a (n - 1) - 4 * a (n - 3) + a (n - 4) + a (n - 5)) ∧
    (mk a = invOfUnit (1 - C 3 * X + C 4 * X ^ 3 - X ^ 4 - X ^ 5) 1 *
      (1 + X - X ^ 2 - X ^ 3 + X ^ 4 + X ^ 6)) := by
  sorry

end OMA.S_oeis_a020964
