import Mathlib

/-!
# Mathar's recurrence for OEIS A306948

Ilya Gutkovskiy defined the sequence by its exponential generating function.
R. J. Mathar conjectured the recurrence on August 20, 2021.
All five indices occur for n ≥ 4.

Source: https://oeis.org/A306948
Credit: @mmiranda2
-/

namespace OMA.S_oeis_a306948

open PowerSeries

noncomputable def egf : PowerSeries ℚ := (1 + X) * log ℚ * exp ℚ

noncomputable def a (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n egf

theorem main : ∀ n : ℕ, 4 ≤ n →
    a n + ((n : ℚ) - 5) * a (n - 1) + (-3 * n + 10 : ℚ) * a (n - 2) +
      3 * ((n : ℚ) - 3) * a (n - 3) + (-(n : ℚ) + 3) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a306948
