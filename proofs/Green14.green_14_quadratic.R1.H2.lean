import OMAReductions.R_Green14_green_14_quadratic_R1
import Mathlib

-- Step Green14.green_14_quadratic.R1.H2: hypothesis H2 of reduction Green14.green_14_quadratic.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Green14StepH2

open Filter Topology

/-- `exp (c * (log r) ^ (4 / 3 - o r))` with `o → 0` is not bounded by any power of `r`. -/
theorem not_isBigO_pow (c : ℝ) (hc : 0 < c) (o : ℕ → ℝ) (ho : Tendsto o atTop (𝓝 0)) (d : ℕ) :
    ¬ (fun (r : ℕ) => Real.exp (c * (Real.log r) ^ (4 / 3 - o r))) =O[atTop]
      fun (r : ℕ) => (r : ℝ) ^ d := by
  intro hO
  obtain ⟨C, hCpos, hC⟩ := hO.exists_pos
  have hbound := hC.bound
  have ho' : ∀ᶠ r : ℕ in atTop, o r < 1 / 12 := (tendsto_order.1 ho).2 (1 / 12) (by norm_num)
  have hlog : Tendsto (fun r : ℕ => Real.log (r : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL1 : ∀ᶠ r : ℕ in atTop, 1 ≤ Real.log (r : ℝ) := hlog.eventually_ge_atTop 1
  have hroot : Tendsto (fun r : ℕ => (Real.log (r : ℝ)) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hlog
  have hq : ∀ᶠ r : ℕ in atTop, ((d : ℝ) + |Real.log C| + 1) / c ≤ (Real.log (r : ℝ)) ^ (1 / 4 : ℝ) :=
    hroot.eventually_ge_atTop _
  have hr1 : ∀ᶠ r : ℕ in atTop, 1 ≤ r := eventually_ge_atTop 1
  obtain ⟨r, hb, hor, hL, hqr, hr⟩ := (hbound.and (ho'.and (hL1.and (hq.and hr1)))).exists
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hpowpos : (0 : ℝ) < (r : ℝ) ^ d := pow_pos hrpos d
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos hpowpos] at hb
  have h1 : c * (Real.log r) ^ (4 / 3 - o r) ≤ Real.log C + d * Real.log r := by
    have h := (Real.le_log_iff_exp_le (mul_pos hCpos hpowpos)).mpr hb
    rwa [Real.log_mul hCpos.ne' hpowpos.ne', Real.log_pow] at h
  have hLpos : 0 < Real.log (r : ℝ) := by linarith
  have h2 : (Real.log r) ^ (5 / 4 : ℝ) ≤ (Real.log r) ^ (4 / 3 - o r) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have h3 : (Real.log r) ^ (5 / 4 : ℝ) = Real.log r * (Real.log r) ^ (1 / 4 : ℝ) := by
    have e : (5 / 4 : ℝ) = 1 + 1 / 4 := by norm_num
    rw [e, Real.rpow_add hLpos, Real.rpow_one]
  have h4 : (d : ℝ) + |Real.log C| + 1 ≤ c * (Real.log (r : ℝ)) ^ (1 / 4 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hqr hc.le
    rwa [mul_div_cancel₀ _ hc.ne'] at this
  have h5 : Real.log r * ((d : ℝ) + |Real.log C| + 1) ≤
      Real.log r * (c * (Real.log (r : ℝ)) ^ (1 / 4 : ℝ)) :=
    mul_le_mul_of_nonneg_left h4 hLpos.le
  have h6 : |Real.log C| ≤ Real.log r * |Real.log C| :=
    le_mul_of_one_le_left (abs_nonneg _) hL
  have h7 : c * (Real.log r) ^ (5 / 4 : ℝ) ≤ c * (Real.log r) ^ (4 / 3 - o r) :=
    mul_le_mul_of_nonneg_left h2 hc.le
  have h8 := le_abs_self (Real.log C)
  rw [h3] at h7
  nlinarith

end Green14StepH2

theorem OMA.solution : OMA.R_Green14_green_14_quadratic_R1.H2 :=
  fun c hc o ho d => Green14StepH2.not_isBigO_pow c hc o ho d
