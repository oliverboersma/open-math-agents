import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Rat.Defs

/-!
# A054341, row sums of a central binomial convolution triangle

Paul Barry's generating function on the OEIS entry is
C(x²)/(1−2xC(x²)), where C(x) is the ordinary Catalan generating function.
Expansion by two substitutes x² for x. All coefficients are taken over ℚ.
In Mathar's 2012 recurrence put n=t+3, the full range at offset zero.

Source: https://oeis.org/A054341
Triangle: https://oeis.org/A054336
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a054341

open PowerSeries

noncomputable def doubleCatalan : PowerSeries ℚ :=
  expand 2 (by decide) (map (Nat.castRingHom ℚ) catalanSeries)

noncomputable def series : PowerSeries ℚ :=
  doubleCatalan * (1 - 2 * X * doubleCatalan)⁻¹

noncomputable def a (n : ℕ) : ℚ := coeff n series

theorem main : ∀ t : ℕ,
    2*((t:ℚ)+4)*a (t+3) - 5*((t:ℚ)+4)*a (t+2) -
      8*((t:ℚ)+1)*a (t+1) + 20*((t:ℚ)+1)*a t = 0 := by
  sorry

end OMA.S_oeis_a054341
