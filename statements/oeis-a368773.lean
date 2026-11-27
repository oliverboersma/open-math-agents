import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Mathar's recurrence for A368773

Source: https://oeis.org/A368773
The recurrence starts at index 4, so all indices are nonnegative.
-/

namespace OMA.S_oeis_a368773

open PowerSeries

noncomputable def radical : PowerSeries ℚ :=
  PowerSeries.subst (-10 * X ^ 2 + 9 * X ^ 4 : PowerSeries ℚ) (binomialSeries ℚ (1 / 2 : ℚ))

noncomputable def B : PowerSeries ℚ := radical * (1 - 3 * X)⁻¹

/-- Coefficients of the even part of the published packing-path series. -/
noncomputable def a (n : ℕ) : ℚ := coeff (n + 1) (B - 1 + X) / 4

theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) + 1) * a n - 3 * a (n - 1) + (-(10 : ℚ) * n + 11) * a (n - 2) +
      3 * a (n - 3) + 9 * ((n : ℚ) - 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a368773
