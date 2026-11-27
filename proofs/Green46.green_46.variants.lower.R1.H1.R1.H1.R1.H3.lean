import OMAReductions.R_Green46_green_46_variants_lower_R1_H1_R1_H1_R1
import Mathlib

-- Step Green46.green_46.variants.lower.R1.H1.R1.H1.R1.H3: hypothesis H3 of reduction Green46.green_46.variants.lower.R1.H1.R1.H1.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset Filter Real
open scoped Classical

/-! With L = log X and U = log L: eventually L^4 ≤ X, 8 c L ≤ X and 40 c U ≥ 2. Since
log U < U the first quantity is at most 4 c X L < X^2. Since U ≤ L, U^3 ≤ X/L, so the left
side of the second inequality is at most 2 X/L ≤ 40 c U X/L. -/

theorem OMA.solution : OMA.R_Green46_green_46_variants_lower_R1_H1_R1_H1_R1.H3 := by
  intro c hc
  have hR : ∀ᶠ X : ℝ in atTop, 4*(c*X*log X*log (log (log X))/log (log X)) < X*X ∧
      (log (log X))^3 + X/log X ≤ 40*c*X*log (log X)/log X := by
    have h1 : ∀ᶠ X : ℝ in atTop, log X ^ 4 ≤ X := by
      filter_upwards [(isLittleO_pow_log_id_atTop (n := 4)).bound one_pos, eventually_ge_atTop (1:ℝ)]
        with X hX hX1
      have h0 : 0 ≤ log X := log_nonneg hX1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 4), id,
        abs_of_nonneg (by linarith), one_mul] at hX
      exact hX
    have h2 : ∀ᶠ X : ℝ in atTop, log X ≤ 1/(8*c) * X := by
      filter_upwards [isLittleO_log_id_atTop.bound (show (0:ℝ) < 1/(8*c) by positivity),
        eventually_ge_atTop (1:ℝ)] with X hX hX1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (log_nonneg hX1), id,
        abs_of_nonneg (by linarith)] at hX
      exact hX
    have hll : Tendsto (fun X : ℝ => log (log X)) atTop atTop :=
      tendsto_log_atTop.comp tendsto_log_atTop
    filter_upwards [h1, h2, hll.eventually_ge_atTop (1/(20*c)), hll.eventually_ge_atTop 1,
      eventually_gt_atTop (1:ℝ)] with X h1 h2 h3 h4 hX
    have hL : 0 < log X := log_pos hX
    have hX0 : 0 < X := by linarith
    set L := log X with hLdef
    set U := log L with hUdef
    have hU0 : 0 < U := by linarith
    have hUL : U ≤ L := by
      have := Real.log_le_sub_one_of_pos hL
      linarith
    constructor
    · have hlogU : log U / U < 1 := by
        rw [div_lt_one hU0]
        have := Real.log_le_sub_one_of_pos hU0
        linarith
      have hpos : 0 < c*X*L := by positivity
      calc 4*(c*X*L*log U/U) = 4*(c*X*L)*(log U/U) := by ring
        _ ≤ 4*(c*X*L)*1 := by
          apply mul_le_mul_of_nonneg_left hlogU.le (by positivity)
        _ < X*X := by
          have : 8*c*L ≤ X := by
            have := mul_le_mul_of_nonneg_left h2 (show (0:ℝ) ≤ 8*c by positivity)
            rw [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
            linarith
          nlinarith
    · have hU3 : U^3 ≤ X/L := by
        rw [le_div_iff₀ hL]
        calc U^3 * L ≤ L^3 * L := by
              apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hU0.le hUL 3) hL.le
          _ = L^4 := by ring
          _ ≤ X := h1
      have h40 : 2 ≤ 40*c*U := by
        have := mul_le_mul_of_nonneg_left h3 (show (0:ℝ) ≤ 40*c by positivity)
        rw [show 40*c*(1/(20*c)) = 2 by field_simp; norm_num] at this
        linarith
      have hXL : 0 ≤ X/L := by positivity
      calc U^3 + X/L ≤ 2*(X/L) := by linarith
        _ ≤ (40*c*U)*(X/L) := mul_le_mul_of_nonneg_right h40 hXL
        _ = 40*c*X*U/L := by ring
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hR] with x hx
  exact hx
