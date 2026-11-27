import OMAReductions.R_Erdos420_erdos_420_variants_log_frequently_lt_two_R1
import Mathlib

-- Step Erdos420.erdos_420.variants.log_frequently_lt_two.R1.H3: hypothesis H3 of reduction
-- Erdos420.erdos_420.variants.log_frequently_lt_two.R1
-- Credit: @ivillar

/-!
Put `u = log log log m → ∞`. Then `log log m = exp u ≥ u⁴ / 24` and `log u ≥ 1` once `u ≥ e`,
so `log log m · log u / (9 u³) ≥ u / 216 ≥ c` once also `u ≥ 216 c`; multiply by `log m > 0`.
-/

open Filter in
theorem OMA.solution : OMA.R_Erdos420_erdos_420_variants_log_frequently_lt_two_R1.H3 := by
  unfold OMA.R_Erdos420_erdos_420_variants_log_frequently_lt_two_R1.H3
  intro c hc
  have h0 : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun m : ℕ => Real.log (Real.log (m : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp h0
  have h1 : Tendsto (fun m : ℕ => Real.log (Real.log (Real.log (m : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp h2
  filter_upwards [h1.eventually_ge_atTop (max (Real.exp 1) (216 * c)),
    h2.eventually_gt_atTop 0, h0.eventually_gt_atTop 0] with m hu hL2 hL1
  set L1 := Real.log (m : ℝ) with hL1def
  set L2 := Real.log L1 with hL2def
  set u := Real.log L2 with hudef
  have hue : Real.exp 1 ≤ u := le_trans (le_max_left _ _) hu
  have huc : 216 * c ≤ u := le_trans (le_max_right _ _) hu
  have hupos : 0 < u := lt_of_lt_of_le (Real.exp_pos 1) hue
  have hL2eq : L2 = Real.exp u := (Real.exp_log hL2).symm
  have hL4 : 1 ≤ Real.log u := by
    rw [Real.le_log_iff_exp_le hupos]
    exact hue
  have hexp : u ^ 4 / 24 ≤ Real.exp u := by
    have h := Real.pow_div_factorial_le_exp (x := u) (hx := hupos.le) (n := 4)
    norm_num [Nat.factorial] at h
    exact h
  have h3 : c * (9 * u ^ 3) ≤ u ^ 4 / 24 := by
    nlinarith [mul_le_mul_of_nonneg_right huc (pow_nonneg hupos.le 3)]
  have h4 : c * (9 * u ^ 3) ≤ L2 * Real.log u := by
    rw [hL2eq]
    calc c * (9 * u ^ 3) ≤ u ^ 4 / 24 := h3
      _ ≤ Real.exp u := hexp
      _ ≤ Real.exp u * Real.log u := le_mul_of_one_le_right (Real.exp_pos u).le hL4
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h4 hL1.le]
