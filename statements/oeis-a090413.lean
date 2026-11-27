import Mathlib

/-!
# OEIS A090413, the Chebyshev transform of powers of three

Source: https://oeis.org/A090413

The sequence is defined by the ordinary generating function given in the entry.
The fourth term in the conjectured relation has index n-3, so the relation
starts at n=3.
-/

namespace OMA.S_oeis_a090413

open PowerSeries

noncomputable def catNeg : PowerSeries ℚ :=
  (catalanSeries.map (Nat.castRingHom ℚ)).subst (-(X : PowerSeries ℚ)^2)

noncomputable def series : PowerSeries ℚ :=
  catNeg * (1 - 3 * X * catNeg)⁻¹

noncomputable def term (n : ℕ) : ℚ := coeff n series

theorem main : ∀ n : ℕ, 3 ≤ n →
    3*((n:ℚ)+1)*term n - 8*((n:ℚ)+1)*term (n-1) +
      12*((n:ℚ)-2)*term (n-2) + 32*(2-(n:ℚ))*term (n-3) = 0 := by
  sorry

end OMA.S_oeis_a090413
