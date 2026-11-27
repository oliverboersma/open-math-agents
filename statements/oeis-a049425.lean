import Mathlib

/-!
# Mathar's recurrence for A049425

Source: https://oeis.org/A049425
Conjecture: R. J. Mathar, November 14, 2011.
Proof in the OEIS entry: Emanuele Munarini, October 20, 2014.

A049425 has exponential generating function exp(x + x² + x³/3).
Thus a(n) is n factorial times the coefficient of xⁿ. The recurrence
is stated at index n+3 so every index is in the domain.
-/

namespace OMA.S_oeis_a049425
open PowerSeries

noncomputable def parameter : PowerSeries ℚ := X + X^2 + C (1/3) * X^3

noncomputable def series : PowerSeries ℚ := (PowerSeries.exp ℚ).subst parameter

noncomputable def a (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n series

theorem main : ∀ n : ℕ, a (n+3) = a (n+2) + 2*((n:ℚ)+2)*a (n+1) +
    ((n:ℚ)+2)*((n:ℚ)+1)*a n := by
  sorry

end OMA.S_oeis_a049425
