import OMAReductions.R_PartitionParity_zheng_odd_R1
import Mathlib

-- Step PartitionParity.zheng.odd.R1.H2: hypothesis H2 of reduction PartitionParity.zheng.odd.R1
-- Credit: @ivillar

/-!
# A positive lower limit of `f X / √X` gives `√X = O(f X)`

If the lower limit is at least `c > 0`, then eventually `f X / √X > c / 2`, so
`√X ≤ (2 / c) * f X` for large `X`.
-/

namespace PartitionParityLiminfStep

open Filter Asymptotics

theorem isBigO_of_liminf : ∀ (f : ℝ → ℝ) (c : ℝ), 0 < c →
    ((c : ℝ) : EReal) ≤ liminf (fun X : ℝ ↦ ((f X / Real.sqrt X : ℝ) : EReal)) atTop →
    (fun X : ℝ ↦ Real.sqrt X) =O[atTop] f := by
  intro f c hc hlim
  have hlt : ((c / 2 : ℝ) : EReal) <
      liminf (fun X : ℝ ↦ ((f X / Real.sqrt X : ℝ) : EReal)) atTop :=
    lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (by linarith)) hlim
  have hev := eventually_lt_of_lt_liminf hlt
  refine IsBigO.of_bound (2 / c) ?_
  filter_upwards [hev, eventually_gt_atTop 0] with X hX hX0
  have h1 : c / 2 < f X / Real.sqrt X := EReal.coe_lt_coe_iff.mp hX
  have hs : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have h2 : c / 2 * Real.sqrt X < f X := (lt_div_iff₀ hs).mp h1
  have hf : 0 < f X := lt_trans (by positivity) h2
  rw [Real.norm_of_nonneg hs.le, Real.norm_of_nonneg hf.le]
  have h3 : Real.sqrt X = 2 / c * (c / 2 * Real.sqrt X) := by
    field_simp
  rw [h3]
  exact mul_le_mul_of_nonneg_left h2.le (by positivity)

end PartitionParityLiminfStep

theorem OMA.solution : OMA.R_PartitionParity_zheng_odd_R1.H2 :=
  PartitionParityLiminfStep.isBigO_of_liminf
