import Mathlib

/-!
# MathOverflow 335876

Source: https://mathoverflow.net/questions/335876
-/

namespace OMA.S_mo_335876

open Filter Set Topology

def hasDirectionalDerivative {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x v : E) (L : ℝ) : Prop :=
  Tendsto (fun t : ℝ => (f (x + t • v) - f x) / t) (𝓝[>] 0) (𝓝 L)

theorem main : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E],
    ∀ f : E → ℝ, ∀ x : E, IsLocalMin f x →
    ∀ v : E, ∀ L : ℝ, hasDirectionalDerivative f x v L → L = 0 := by
  sorry

end OMA.S_mo_335876
