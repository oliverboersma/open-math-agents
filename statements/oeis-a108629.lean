import Mathlib

/-!
R. J. Mathar's recurrence for OEIS A108629, proposed January 24, 2020.
The sequence starts at index one. The constant coefficient is zero.
The binomial series with exponent one half selects the square root with
constant coefficient one in the defining ordinary generating function.
Source: https://oeis.org/A108629
-/

namespace OMA.S_oeis_a108629

open PowerSeries

noncomputable def radicandTail : PowerSeries ℚ :=
  -2 * X - 3 * X ^ 2 - 4 * X ^ 3

noncomputable def rootSeries : PowerSeries ℚ :=
  PowerSeries.subst radicandTail (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ))

noncomputable def series : PowerSeries ℚ :=
  (1 + X - rootSeries) * (2 * (1 + X + X ^ 2))⁻¹

noncomputable def a (n : ℕ) : ℚ := PowerSeries.coeff n series

theorem main : ∀ n : ℕ, 6 ≤ n →
    (n : ℚ) * a n =
      ((n : ℚ) - 3) * a (n - 1) + 4 * ((n : ℚ) - 3) * a (n - 2) +
      3 * (3 * (n : ℚ) - 10) * a (n - 3) + (7 * (n : ℚ) - 27) * a (n - 4) +
      2 * (2 * (n : ℚ) - 9) * a (n - 5) := by
  sorry

end OMA.S_oeis_a108629
