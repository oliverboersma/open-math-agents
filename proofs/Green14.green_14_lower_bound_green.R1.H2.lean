import OMAReductions.R_Green14_green_14_lower_bound_green_R1
import Mathlib

-- Step Green14.green_14_lower_bound_green.R1.H2: hypothesis H2 of reduction Green14.green_14_lower_bound_green.R1
-- Credit: @ivillar

/-!
# Comparing the two stretched exponentials

For `r ≥ 3` we have `log r ≥ 1`, so `(log r) ^ (4 / 3 - o r) ≤ (log r) ^ (2 - o r)`, and the
exponentials compare with constant `1`.
-/

namespace Green14CompareStep

open Filter Topology

theorem compare : ∀ c : ℝ, 0 < c → ∀ o : ℕ → ℝ,
  (fun (r : ℕ) => Real.exp (c * (Real.log r) ^ (4 / 3 - o r))) =O[atTop]
    fun (r : ℕ) => Real.exp (c * (Real.log r) ^ (2 - o r)) := by
  intro c hc o
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 3] with r hr
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]
  apply Real.exp_le_exp.mpr
  have h3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hlog : (1 : ℝ) ≤ Real.log (r : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_three
    linarith
  have hpow : Real.log (r : ℝ) ^ (4 / 3 - o r) ≤ Real.log (r : ℝ) ^ (2 - o r) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by linarith)
  exact mul_le_mul_of_nonneg_left hpow hc.le

end Green14CompareStep

theorem OMA.solution : OMA.R_Green14_green_14_lower_bound_green_R1.H2 :=
  Green14CompareStep.compare
