import Mathlib

/-!
# Zeros of sums and differences of stretched Riemann ξ-functions

Source: https://mathoverflow.net/questions/196613
Credit: @PastaPastaPasta
-/

namespace OMA.S_mo_196613

/-- Riemann's entire ξ-function, including its value 1/2 at both 0 and 1.
Mathlib's entire completion is Λ(s) + 1/s + 1/(1-s). -/
noncomputable def xi (s : ℂ) : ℂ :=
  (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2

/-- For every nonzero real stretch, every zero of either sign lies on the critical line. -/
theorem main : ∀ a : ℝ, a ≠ 0 → ∀ s : ℂ,
    xi (a * s) + xi (a * (1 - s)) = 0 ∨
    xi (a * s) - xi (a * (1 - s)) = 0 → s.re = 1 / 2 := by
  sorry

end OMA.S_mo_196613
