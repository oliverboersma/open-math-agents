import Mathlib

/-!
# MathOverflow 201602

Source: https://mathoverflow.net/questions/201602
-/

namespace OMA.S_mo_201602

open Filter MeasureTheory
open scoped Topology

theorem main : ∀ (laws : ℕ → ProbabilityMeasure ℝ) (law : ProbabilityMeasure ℝ),
    Tendsto laws atTop (𝓝 law) →
    ∀ t : ℝ, Tendsto (fun n => charFun (laws n : Measure ℝ) t) atTop (𝓝 (charFun (law : Measure ℝ) t)) := by
  sorry

end OMA.S_mo_201602
