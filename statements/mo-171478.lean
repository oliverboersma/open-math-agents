import Mathlib

/-!
# MathOverflow 171478

Source: https://mathoverflow.net/questions/171478
-/

namespace OMA.S_mo_171478

def boundedOnBalls {H : Type} [NormedAddCommGroup H] (f : H → H) : Prop :=
  ∀ R : ℝ, ∃ M : ℝ, ∀ x : H, ‖x‖ ≤ R → ‖f x‖ ≤ M

def coercive {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : H → H) : Prop :=
  ∀ B : ℝ, ∃ R : ℝ, ∀ x : H, R ≤ ‖x‖ → B ≤ inner ℝ (f x) x / ‖x‖

theorem main : ∃ (H : Type) (normed : NormedAddCommGroup H),
    letI := normed
    ∃ innerSpace : InnerProductSpace ℝ H,
    letI := innerSpace
    ∃ _ : CompleteSpace H, ∃ f : H → H,
      boundedOnBalls f ∧ Continuous f ∧
      (∀ x y, 0 ≤ inner ℝ (f x - f y) (x - y)) ∧ ¬ coercive f ∧ ¬ Function.Surjective f := by
  sorry

end OMA.S_mo_171478
