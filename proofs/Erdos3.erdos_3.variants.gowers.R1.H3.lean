import OMAReductions.R_Erdos3_erdos_3_variants_gowers_R1
import Mathlib

/-!
Step H3 of Erdos3.erdos_3.variants.gowers.R1. Since log t = o(t^c), eventually
a log t ≤ t^c, which is exp (-(t^c)) ≤ exp (-a log t) = t^(-a).
-/

open Filter in
theorem OMA.solution : OMA.R_Erdos3_erdos_3_variants_gowers_R1.H3 := by
  unfold OMA.R_Erdos3_erdos_3_variants_gowers_R1.H3
  intro c a hc ha
  have h := (isLittleO_log_rpow_atTop hc).bound (show 0 < 1 / a by positivity)
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with t ht ht1
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht1
  rw [Real.norm_of_nonneg hl.le, Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)] at ht
  have key : a * Real.log t ≤ t ^ c := by
    calc a * Real.log t ≤ a * (1 / a * t ^ c) := mul_le_mul_of_nonneg_left ht ha.le
      _ = t ^ c := by field_simp
  rw [Real.rpow_def_of_pos ht0 (-a)]
  apply Real.exp_le_exp.mpr
  linarith
