import OMAReductions.R_SatoTateConjecture_satoTate_conjecture_R1
import Mathlib

-- Step SatoTateConjecture.satoTate_conjecture.R1.H2: hypothesis H2 of reduction SatoTateConjecture.satoTate_conjecture.R1
-- Credit: @ivillar

/-!
# The Sato-Tate interval mass as an angular integral

Both sides have closed forms: `∫ sin ^ 2` is given by `integral_sin_sq`, the values of `sin` and
`cos` at `arccos` are `√(1 - x ^ 2)` and `x`, and `arcsin x = π / 2 - arccos x`.
-/

namespace SatoTateMassStep

open Real SatoTateConjecture

theorem st_mass : ∀ a b : ℝ, -1 ≤ a → a ≤ b → b ≤ 1 →
    2 / π * (∫ θ in arccos b..arccos a, sin θ ^ 2) = satoTateMeasure a b := by
  intro a b ha hab hb
  have ha1 : a ≤ 1 := hab.trans hb
  have hb1 : -1 ≤ b := ha.trans hab
  have hpi : π ≠ 0 := pi_ne_zero
  rw [integral_sin_sq, sin_arccos, sin_arccos, cos_arccos hb1 hb, cos_arccos ha ha1]
  unfold satoTateMeasure satoTateCDF
  rw [arcsin_eq_pi_div_two_sub_arccos, arcsin_eq_pi_div_two_sub_arccos]
  field_simp
  ring

end SatoTateMassStep

theorem OMA.solution : OMA.R_SatoTateConjecture_satoTate_conjecture_R1.H2 :=
  SatoTateMassStep.st_mass
