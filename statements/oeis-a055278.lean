import Mathlib

/-!
# A055278: Number of rooted trees with n nodes and 3 leaves.

Source: https://oeis.org/A055278
Credit: @rot13maxi

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a055278

/-- A055278: number of rooted trees with `n` nodes and `3` leaves.
OEIS gives the explicit formula `(3*n^4 - 20*n^3 + 54*n^2 - 60*n + 32) / 144`. -/
def A055278 (n : ℕ) : ℤ :=
  (3 * n ^ 4 - 20 * n ^ 3 + 54 * n ^ 2 - 60 * n + 32) / 144

/-- Ralf Stephan's conjectured g.f. for A055278:
`x^4*(x^3+x^2+1) / ((1-x^2)*(1-x^3)*(1-x)^3)`.
Multiplying by the denominator (constant term `1`) gives the equivalent
coefficient identity stated below. -/
theorem main :
    (PowerSeries.mk fun n => (A055278 (n + 4) : ℚ)) *
      ((1 - (PowerSeries.X : PowerSeries ℚ) ^ 2) *
        (1 - (PowerSeries.X : PowerSeries ℚ) ^ 3) *
        (1 - (PowerSeries.X : PowerSeries ℚ)) ^ 3) =
      ((PowerSeries.X : PowerSeries ℚ) ^ 3 + (PowerSeries.X : PowerSeries ℚ) ^ 2 + 1) := by
  sorry

end OMA.S_oeis_a055278
