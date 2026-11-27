import Mathlib.RingTheory.PowerSeries.Inverse

/-! Arie Bos's A003477 identity with the other OEIS sequence A077854.
Both sequences start at index zero. The stated sum misses the constant term. -/

namespace OMA.S_oeis_a003477

open PowerSeries Finset
open scoped PowerSeries

private noncomputable def common : ℤ⟦X⟧ := (1 - C 2 * X) * (1 + X ^ 2)
private noncomputable def firstFactor : ℤ⟦X⟧ := 1 - X - C 2 * X ^ 3
private noncomputable def secondFactor : ℤ⟦X⟧ := 1 - X

private noncomputable def firstSeries : ℤ⟦X⟧ := invOfUnit (common * firstFactor) 1
private noncomputable def secondSeries : ℤ⟦X⟧ := invOfUnit (common * secondFactor) 1

/-- A003477 is the coefficient sequence of its OEIS generating function. -/
noncomputable def a (n : ℕ) : ℤ := coeff n firstSeries

/-- A077854 is the coefficient sequence of its OEIS generating function. -/
noncomputable def b (n : ℕ) : ℤ := coeff n secondSeries

theorem main : ∀ n : ℕ, 4 ≤ n →
    a n = b n + 2 * (∑ j ∈ range (n - 3), a (j + 1)) := by
  sorry

end OMA.S_oeis_a003477
