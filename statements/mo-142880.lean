import Mathlib.Probability.BrownianMotion.Basic

/-!
# Signed locations of discrete and continuous maxima, MathOverflow 142880

The edited question asks for affine stochastic domination. D and T are
measurable versions of the signed maximizing locations, which are unique
almost surely under the specified laws. The constants may depend on the drift.
The two processes on nonnegative time are the independent arms.
-/

namespace OMA.S_mo_142880

open MeasureTheory ProbabilityTheory

noncomputable def height {Ω : Type*} (B : ℝ → Ω → ℝ) (d t : ℝ) (ω : Ω) : ℝ :=
  B t ω - d * |t|

theorem main :
    ∀ d : ℝ, 0 < d → ∃ a b : ℝ, 0 < a ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ → Ω → ℝ),
        IsBrownianReal (fun t : NNReal => B (t : ℝ)) P →
        IsBrownianReal (fun t : NNReal => B (-(t : ℝ))) P →
        IndepFun (fun ω (t : NNReal) => B (t : ℝ) ω)
          (fun ω (t : NNReal) => B (-(t : ℝ)) ω) P →
        ∀ (D : Ω → ℤ) (T : Ω → ℝ), AEMeasurable D P → AEMeasurable T P →
          (∀ᵐ ω ∂P, ∀ n : ℤ, height B d n ω ≤ height B d (D ω) ω) →
          (∀ᵐ ω ∂P, ∀ t : ℝ, height B d t ω ≤ height B d (T ω) ω) →
          ∀ x : ℝ, P {ω | x < (D ω : ℝ)} ≤ P {ω | x < a * T ω + b} := by
  sorry

end OMA.S_mo_142880
