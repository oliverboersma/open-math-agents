import Mathlib

/-!
# MathOverflow 308189

Source: https://mathoverflow.net/questions/308189
-/

namespace OMA.S_mo_308189

open Polynomial

def circleNorms (P : ℂ[X]) : Set ℝ :=
  { t | ∃ w : ℂ, ‖w‖ = 1 ∧ ‖P.eval w‖ = t }

noncomputable def rotationBound (P : ℂ[X]) : ℝ :=
  P.natDegree - (‖P.coeff 0‖ - 1) / (‖P.coeff 0‖ + 1)

theorem main : ∀ P : ℂ[X], 1 ≤ P.natDegree →
    (∀ w : ℂ, ‖w‖ < 1 → P.eval w ≠ 0) →
    ∃ M : ℝ, IsGreatest (circleNorms P) M ∧
      ∀ α z : ℂ, ‖α‖ = 1 → ‖z‖ = 1 →
        ‖α * z * P.derivative.eval z + z * P.derivative.eval z -
          (rotationBound P : ℂ) * P.eval z‖ ≤ rotationBound P * M := by
  sorry

end OMA.S_mo_308189
